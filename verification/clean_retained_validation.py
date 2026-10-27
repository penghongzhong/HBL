#!/usr/bin/env python3
"""Rebuild HBL from tracked source without reusing project objects.

Third-party pinned package caches remain available. No proof source is changed.
The broad build and each strict terminal check have independent exit statuses.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from proofchain_scan import ROOTS, mask_comments_and_strings

TARGETS = {
    'KinematicPhysicalTimeInverseDeriv': 'HBL.Kinematic',
    'KinematicPhysicalDynamics': 'HBL.Kinematic',
    'TriangularReconstruction': 'HBL.Modulation.TriangularRepair',
    'PhysicalWeakRadial': 'HBL.Modulation.Monopole',
    'WeightedJointBackward': 'HBL.MainBackward',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
EVIDENCE = Path('evidence')
REPORT = Path('verification/clean-retained-current-status.json')
ERRORS = Path('verification/clean-retained-current-errors.json')


def source_hashes() -> dict[str, str]:
    names = subprocess.check_output(['git', 'ls-files', '*.lean', 'lean-toolchain', 'lake-manifest.json'], text=True).splitlines()
    return {n: hashlib.sha256(Path(n).read_bytes()).hexdigest() for n in names}


def run(command: list[str], name: str) -> tuple[int, str]:
    path = EVIDENCE / name
    with path.open('w') as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    return result.returncode, re.sub(r'\x1b\[[0-9;]*m', '', path.read_text())


def error_blocks(text: str) -> list[str]:
    blocks, current = [], []
    for line in text.splitlines():
        boundary = (re.match(r'(?:error|warning|info): ', line) or line.startswith('trace:')
                    or any(word in line for word in (' Built ', ' Building ', ' Replayed ')))
        if boundary:
            if current:
                blocks.append('\n'.join(current)); current = []
            if line.startswith('error:'):
                current = [line]
        elif current:
            current.append(line)
    if current:
        blocks.append('\n'.join(current))
    return blocks


def main() -> None:
    EVIDENCE.mkdir(exist_ok=True)
    before = source_hashes()
    dirty = subprocess.check_output(['git', 'diff', '--name-only', '--', '*.lean', 'lean-toolchain', 'lake-manifest.json'], text=True)
    if dirty:
        raise RuntimeError('Tracked Lean source differs from the checked-out revision: '+dirty)
    project_objects = Path('.lake/build')
    if project_objects.is_symlink():
        raise RuntimeError('Refuse to remove a symlinked project build directory')
    cached_count = len(list(project_objects.rglob('*.olean'))) if project_objects.exists() else 0
    shutil.rmtree(project_objects, ignore_errors=False) if project_objects.exists() else None
    assert not project_objects.exists()
    report = {
        'source_commit': os.environ.get('GITHUB_SHA', subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()),
        'run_id': os.environ.get('GITHUB_RUN_ID'),
        'project_build_directory_removed_before_validation': True,
        'project_cached_olean_files_removed': cached_count,
        'third_party_dependency_caches_retained': True,
        'protected_roots': ROOTS,
        'main_theorem_closed': False,
        'new_original_environments_verified': 0,
        'full_paper_percentage_recertified': False,
        'strict_targets': {},
    }
    start = time.time()
    broad_exit, broad_log = run(['lake', 'build', 'HBL', 'HBL.SpectralBridgeTypes', *ROOTS], 'clean-retained-build.log')
    report['clean_retained_build_exit'] = broad_exit
    report['clean_retained_build_seconds'] = round(time.time()-start, 2)
    report['failed_module_files'] = sorted(set(re.findall(r'^error: HBL/([^:]+):', broad_log, re.M)))
    errors = {'source_commit': report['source_commit'], 'run_id': report['run_id'], 'broad_build_errors': error_blocks(broad_log), 'strict_targets': {}}
    for module, namespace in TARGETS.items():
        source = Path('HBL') / (module+'.lean')
        clean = mask_comments_and_strings(source.read_text())
        names = [namespace+'.'+n for n in re.findall(r'^(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_\']*)', clean, re.M)]
        row = {'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'declarations': names,
               'build_exit': None, 'strict_source_exit': None, 'audit_exit': None, 'audit_passed': False}
        built, build_log = run(['lake', 'build', 'HBL.'+module], module+'-build.log')
        row['build_exit'] = built
        errors['strict_targets'][module] = error_blocks(build_log)
        if built == 0:
            strict, strict_log = run(['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true', str(source)], module+'-strict.log')
            row['strict_source_exit'] = strict
            errors['strict_targets'][module] += error_blocks(strict_log)
            if strict == 0:
                audit = 'import HBL.'+module+'\nset_option pp.all true\nset_option pp.maxSteps 10000000\nset_option maxRecDepth 1000000\n'
                audit += '\n'.join('#check @'+name for name in names)+'\n'
                audit += '\n'.join('set_option pp.all false in\n#print axioms '+name for name in names)+'\n'
                audit_path = EVIDENCE / (module+'Audit.lean')
                audit_path.write_text(audit)
                audit_exit, out = run(['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true', str(audit_path)], module+'-types-and-axioms.txt')
                row['audit_exit'] = audit_exit
                pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
                found = [(m.group(1),m.group(2) or '') for m in re.finditer(pattern,out,re.S)]
                row['axioms'] = {n:[x.strip() for x in a.split(',') if x.strip()] for n,a in found}
                row['audit_passed'] = (bool(names) and audit_exit == 0 and [n for n,_ in found] == names
                    and len(set(names)) == len(names)
                    and all(set(a) <= ALLOWED for a in row['axioms'].values())
                    and not any(token in out for token in ['sorryAx','⋯','...'])
                    and not re.search(r'\b(sorry|admit|axiom|unsafe)\b',clean))
                errors['strict_targets'][module] += error_blocks(out)
        report['strict_targets'][module] = row
        REPORT.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
        ERRORS.write_text(json.dumps(errors,ensure_ascii=False,indent=2)+'\n')
        print(module, json.dumps({k:v for k,v in row.items() if k not in ['axioms','declarations']}), flush=True)
    report['tracked_sources_unchanged'] = before == source_hashes()
    report['source_hashes'] = before
    report['all_strict_targets_passed'] = all(row['audit_passed'] for row in report['strict_targets'].values())
    report['validation_passed'] = broad_exit == 0 and report['all_strict_targets_passed'] and report['tracked_sources_unchanged']
    report['boundary'] = 'Build success and strict declarations do not instantiate missing physical propagators, source estimates or the final PDE and initial-data graph.'
    REPORT.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    ERRORS.write_text(json.dumps(errors,ensure_ascii=False,indent=2)+'\n')
    shutil.copy2(REPORT,EVIDENCE / REPORT.name)
    shutil.copy2(ERRORS,EVIDENCE / ERRORS.name)
    print(json.dumps({k:v for k,v in report.items() if k not in ['source_hashes','strict_targets','protected_roots']},ensure_ascii=False,indent=2))

if __name__ == '__main__':
    main()
