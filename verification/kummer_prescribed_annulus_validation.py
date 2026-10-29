#!/usr/bin/env python3
"""Strict incremental validation; reuse only hash-matching prior strict artifacts."""
from pathlib import Path
import gzip
import hashlib
import json
import os
import re
import subprocess
import tempfile
from proofchain_scan import mask_comments_and_strings

BLOCK = 'HBL/KummerPrescribedAnnulus/'
SOURCES = [BLOCK + x + '.lean' for x in [
    'Clip', 'LinearIVP', 'PhysicalDefinitions', 'ActualIVP', 'Wronskian',
    'ActualPair', 'ActualInverse']]
AUDIT = BLOCK + 'PrescribedAudit.lean'
PRIOR = Path('verification/kummer-source-tangents-status.json')
NAMES = ['HBL.Profile.Kummer.' + x for x in [
    'clipRealVector_properties', 'exists_linear_ivp_on_prescribed_interval',
    'exists_actual_kummer_prescribed_ivp', 'kummer_wronskian_ne_on_prescribed_interval',
    'exists_prescribed_bounded_kummer_pair', 'exists_actual_kummer_prescribed_annulus_inverse']]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
EVIDENCE = Path(tempfile.mkdtemp(prefix='hbl-prescribed-annulus-strict-'))
report = dict(validation_passed=False, new_supporting_theorems=6,
              target_original_environment='prop:one-layer-stage3',
              target_original_environment_closed=False,
              newly_accepted_original_environments=0,
              strict_original_environment_count='9/21', main_PDE_theorem_closed=False)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(cmd, name, env=None):
    print('Checking ' + name, flush=True)
    log = EVIDENCE / name
    with log.open('w') as out:
        p = subprocess.run(cmd, stdout=out, stderr=subprocess.STDOUT, env=env, timeout=1200)
    assert p.returncode == 0, str(log)
    return log.read_text()


try:
    report['base_commit'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    compiler = run(['lean', '--version'], 'compiler.txt').strip()
    assert '4.35.0-rc3' in compiler and '470d5ce1400764999581fd26d5d72b00d990b0f4' in compiler
    report['compiler'] = compiler
    prior = json.loads(PRIOR.read_text())
    assert prior['validation_passed']
    revisions = {}
    for p in json.loads(Path('lake-manifest.json').read_text())['packages']:
        revision = subprocess.check_output(['git', '-C', '.lake/packages/' + p['name'],
                                           'rev-parse', 'HEAD'], text=True).strip()
        assert revision == p['rev'] == prior['dependency_revisions'][p['name']]
        revisions[p['name']] = revision
    assert revisions['mathlib'] == 'a98628e16c11f5167f16124105ddce53efa9bfe5'
    report['dependency_revisions'] = revisions
    assert all(digest(f) == h for f, h in prior['source_sha256'].items())
    # Local fast path. Else rebuild the prior strict certificate, then locate its
    # freshly verified artifacts. Never silently fall back to unchecked oleans.
    def matching_cache():
        for root in Path(tempfile.gettempdir()).glob('hbl-kummer-tangent-strict-*'):
            if all((root / Path(f).with_suffix('.olean')).is_file() and
                   digest(root / Path(f).with_suffix('.olean')) == h
                   for f, h in prior['compiled_source_sha256'].items()):
                return root
        return None
    cache = matching_cache()
    if cache is None:
        run(['python3', 'verification/kummer_source_tangents_validation.py'], 'prior-rebuild.log')
        prior = json.loads(PRIOR.read_text())
        assert prior['validation_passed']
        cache = matching_cache()
    assert cache is not None
    report['reused_strict_certificate'] = str(PRIOR)
    report['reused_strict_artifact_count'] = len(prior['compiled_source_sha256'])
    report['reused_source_and_artifact_hashes_verified'] = True
    snapshot = {f: digest(f) for f in SOURCES + [AUDIT]}
    for f in SOURCES + [AUDIT]:
        code = mask_comments_and_strings(Path(f).read_text())
        assert len(re.findall(r'^(?:theorem|lemma) ', code, re.M)) <= 1, f
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', code), f
        assert not re.search(r'set_option\s+(?:linter\.|warningAsError\s+false)', code), f
    audit = Path(AUDIT).read_text()
    assert re.findall(r'^#check @(\S+)', audit, re.M) == NAMES
    assert re.findall(r'^#print axioms (\S+)', audit, re.M) == NAMES
    assert '#check HBL.Profile.Kummer.LocalKummerPair.mk\n' in audit
    definitions = re.findall(r'^#print (?!axioms )(\S+)', audit, re.M)
    reached = set()
    def visit(filename):
        if filename in reached:
            return
        reached.add(filename)
        for module in re.findall(r'^import (HBL\.KummerPrescribedAnnulus\.\S+)',
                                 Path(filename).read_text(), re.M):
            visit(module.replace('.', '/') + '.lean')
    visit(SOURCES[-1])
    assert reached == set(SOURCES), reached
    root = EVIDENCE / 'lib'
    (root / 'HBL').mkdir(parents=True)
    for entry in (cache / 'HBL').iterdir():
        if entry.name != 'KummerPrescribedAnnulus':
            (root / 'HBL' / entry.name).symlink_to(entry.resolve(), target_is_directory=entry.is_dir())
    env = os.environ.copy()
    env['LEAN_PATH'] = str(root) + os.pathsep + subprocess.check_output(
        ['lake', 'env', 'printenv', 'LEAN_PATH'], text=True).strip()
    artifacts = {}
    for f in SOURCES:
        target = root / Path(f).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        run(['lean', '--trust=0', '-DwarningAsError=true', '-o', str(target), f],
            Path(f).stem + '.log', env)
        artifacts[f] = target
    compiled = {f: digest(p) for f, p in artifacts.items()}
    output = run(['lean', '--trust=0', '-DwarningAsError=true', AUDIT], 'audit.txt', env)
    assert not any(x in output for x in ['sorryAx', '⋯', '…'])
    assert all(re.search(r'\b(?:def|structure) ' + re.escape(n) + r'\b', output)
               for n in definitions)
    report['audited_definition_bodies'] = definitions
    report['audited_structure_constructor'] = 'HBL.Profile.Kummer.LocalKummerPair.mk'
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output, re.S)
    assert [n for n, _ in found] == NAMES, found
    report['axioms'] = {}
    for n, axioms in found:
        used = {re.sub(r'\.\{[^}]*\}$', '', x.strip()) for x in axioms.split(',') if x.strip()}
        assert used <= ALLOWED, used
        report['axioms'][n] = sorted(used)
    assert snapshot == {f: digest(f) for f in SOURCES + [AUDIT]}
    assert compiled == {f: digest(p) for f, p in artifacts.items()}
    assert all(digest(f) == h for f, h in prior['source_sha256'].items())
    assert matching_cache() is not None
    artifact = Path('verification/kummer-prescribed-annulus-types-and-axioms.txt.gz')
    artifact.write_bytes(gzip.compress(output.encode(), mtime=0))
    assert gzip.decompress(artifact.read_bytes()) == output.encode()
    report.update(validation_passed=True, one_theorem_per_file=True,
                  isolated_fresh_new_source_compilation=True, audit_exit_code=0,
                  strict_source_exit_codes={f: 0 for f in SOURCES},
                  source_sha256=snapshot, compiled_artifact_sha256=compiled,
                  complete_type_output_artifact=str(artifact),
                  complete_type_output_bytes=len(output.encode()),
                  complete_type_output_sha256=hashlib.sha256(output.encode()).hexdigest(),
                  compressed_output_sha256=digest(artifact),
                  scope='For each fixed real mu/theta and every input 0<d<z, constructs the actual normalized Kummer C2 right inverse on [z-d,z+d], proves boundary uniqueness and stability/residual bounds. The bound may depend on parameters and interval. No compact-parameter uniformity on this prescribed interval, manuscript outgoing-basis identification, weighted overlap, or nonlinear Hartree residual matching is claimed.')
except Exception as exc:
    report['error'] = repr(exc)
Path('verification/kummer-prescribed-annulus-status.json').write_text(
    json.dumps(report, indent=2, ensure_ascii=False) + '\n')
print(json.dumps(report, indent=2, ensure_ascii=False))
raise SystemExit(0 if report['validation_passed'] else 1)
