#!/usr/bin/env python3
"""Validate the native cutoff argument and its real quartic specialization."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

BASE = 'db6be8c0f0a47cfca9dc629d5b96177cd280a6c1'
TARGET = 'HartreeLocalCutoff'
NAMES = ['potential_hasFDerivAt_noncompact', 'quarticPotential_hasFDerivAt_noncompact']


def main():
    Path('evidence').mkdir(exist_ok=True)
    report = {
        'source_commit': os.environ['GITHUB_SHA'], 'run_id': os.environ['GITHUB_RUN_ID'],
        'baseline': BASE, 'validation_passed': False,
        'main_theorem_closed': False, 'new_original_environments_verified': 0,
        'full_paper_percentage_recertified': False,
        'boundary': 'The compact-core approximation premise is removed from the two new terminal derivative theorems by internally constructed cutoffs and local uniform convergence. The field remains C1 with L4 mass, L2 differential, and uniform field/differential bounds. Higher Sobolev realization, full differentiated remainder estimates and the actual constrained evolution are not concluded.',
        'strict_targets': {},
    }
    errors = {}

    def run(cmd, log):
        p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        Path('evidence/' + log).write_text(p.stdout)
        blocks, active = [], []
        for line in p.stdout.splitlines():
            if re.match(r'(?:error|warning|info): ', line) or re.match(r'HBL/.*: (?:error|warning):', line) or line.startswith('trace:') or ' Built ' in line or ' Building ' in line:
                if active:
                    blocks.append('\n'.join(active)); active = []
                if ('error:' in line or 'warning:' in line) and TARGET in line:
                    active = [line]
            elif active:
                active.append(line)
        if active:
            blocks.append('\n'.join(active))
        if p.returncode and not blocks:
            blocks = [p.stdout[-22000:]]
        if blocks:
            errors[log] = '\n\n'.join(blocks)
        return p.returncode, p.stdout

    try:
        preserved = []
        for name in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE], text=True).splitlines():
            if name.endswith('.lean'):
                assert Path(name).read_bytes() == subprocess.check_output(['git', 'show', BASE + ':' + name]), name
                preserved.append(name)
        report['baseline_Lean_sources_byte_identical'] = len(preserved)
        removed = []
        for path in Path('.lake/build').rglob(TARGET + '.*'):
            if path.is_file():
                removed.append(str(path)); path.unlink()
        report['new_target_cached_files_removed'] = removed
        src = Path('HBL/' + TARGET + '.lean').read_text()
        assert re.findall(r'^(?:def|theorem) (\w+)', src, re.M) == NAMES
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', src)
        report['new_source_sha256'] = hashlib.sha256(src.encode()).hexdigest()
        build, _ = run(['lake', 'build', 'HBL.' + TARGET], 'cutoff-build.log')
        report['build_exit'] = build
        if build == 0:
            sys.path.insert(0, 'verification')
            from quartic_gradient_validation import GROUPS
            groups = dict(GROUPS)
            groups[TARGET] = ('HBL.RegularRadiation.LocalCutoff.', NAMES)
            all_ok = True
            for module, (prefix, short) in groups.items():
                code = Path('HBL/' + module + '.lean').read_text()
                assert re.findall(r'^(?:def|theorem) (\w+)', code, re.M) == short, module
                names = [prefix + n for n in short]
                strict, _ = run(['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true', 'HBL/' + module + '.lean'], module + '-strict.log')
                entry = {'strict_exit': strict, 'audit_passed': False, 'source_sha256': hashlib.sha256(code.encode()).hexdigest(), 'declarations': names}
                if strict == 0:
                    audit = 'import HBL.' + module + '\nset_option pp.all true\nset_option pp.maxSteps 10000000\nset_option maxRecDepth 1000000\n'
                    audit += '\n'.join('#check @' + n for n in names) + '\n'
                    audit += '\n'.join('set_option pp.all false in\n#print axioms ' + n for n in names) + '\n'
                    path = Path('evidence/' + module + 'Audit.lean')
                    path.write_text(audit)
                    ae, out = run(['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true', str(path)], module + '-types-and-axioms.txt')
                    found = [(m.group(1), m.group(2) or '') for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", out, re.S)]
                    ok = ae == 0 and [n for n, _ in found] == names and not any(x in out for x in ['sorryAx', '⋯', '...'])
                    ok = ok and all({x.strip() for x in a.split(',') if x.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'} for _, a in found)
                    entry['audit_passed'] = bool(ok)
                    entry['axioms'] = {n: [x.strip() for x in a.split(',') if x.strip()] for n, a in found}
                all_ok = all_ok and entry['audit_passed']
                report['strict_targets'][module] = entry
            if all_ok:
                from proofchain_scan import ROOTS
                regression, _ = run(['lake', 'build', 'HBL', 'HBL.SpectralBridgeTypes', *ROOTS], 'retained-regression.log')
                report['retained_roots_build_exit'] = regression
                report['validation_passed'] = regression == 0
                report['strict_named_declarations'] = sum(len(v[1]) for v in groups.values())
                report['new_public_theorems'] = len(NAMES)
                report['approximation_sequence_input_in_new_terminals'] = False
    except Exception as exc:
        errors['validation-exception'] = repr(exc)
    finally:
        for folder in ['verification', 'evidence']:
            Path(folder + '/local-cutoff-current-status.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
            Path(folder + '/local-cutoff-current-errors.json').write_text(json.dumps(errors, ensure_ascii=False, indent=2) + '\n')
        print(json.dumps(report, ensure_ascii=False, indent=2))
        print(json.dumps(errors, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
