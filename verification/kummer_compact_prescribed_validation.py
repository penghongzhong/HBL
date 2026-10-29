#!/usr/bin/env python3
"""Strict incremental audit of compact-parameter inversion on an input annulus."""
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
SOURCES = [BLOCK + n + '.lean' for n in ['CenteredGrowth', 'UniformPair', 'CompactPair', 'CompactInverse']]
AUDIT = BLOCK + 'CompactPrescribedAudit.lean'
NAMES = ['HBL.Profile.Kummer.' + n for n in [
    'centered_ode_norm_le_exp', 'prescribed_kummer_pair_exp_bound',
    'exists_compact_prescribed_kummer_pair', 'exists_compact_prescribed_kummer_inverse']]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
EVIDENCE = Path(tempfile.mkdtemp(prefix='hbl-compact-prescribed-strict-'))
report = dict(validation_passed=False, new_supporting_theorems=4,
              target_original_environment='prop:one-layer-stage3', target_original_environment_closed=False,
              newly_accepted_original_environments=0, strict_original_environment_count='9/21',
              main_PDE_theorem_closed=False)


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def run(cmd, name, env=None):
    print('Checking ' + name, flush=True)
    log = EVIDENCE / name
    with log.open('w') as out:
        p = subprocess.run(cmd, stdout=out, stderr=subprocess.STDOUT, env=env, timeout=1200)
    assert p.returncode == 0, str(log)
    return log.read_text()


def load_cache(status, pattern, suffix, key, rebuild):
    path = Path('verification') / status
    r = json.loads(path.read_text())
    assert r['validation_passed']
    assert all(digest(f) == h for f, h in r['source_sha256'].items())
    def match():
        for root in Path(tempfile.gettempdir()).glob(pattern):
            lib = root / suffix
            if all((lib / Path(f).with_suffix('.olean')).is_file() and
                   digest(lib / Path(f).with_suffix('.olean')) == h
                   for f, h in r[key].items()):
                return lib
        return None
    cache = match()
    if cache is None:
        run(['python3', 'verification/' + rebuild], status + '-rebuild.log')
        r = json.loads(path.read_text())
        assert r['validation_passed']
        cache = match()
    assert cache is not None, status
    return path, r, cache, key


try:
    report['base_commit'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    compiler = run(['lean', '--version'], 'compiler.txt').strip()
    assert '4.35.0-rc3' in compiler and '470d5ce1400764999581fd26d5d72b00d990b0f4' in compiler
    report['compiler'] = compiler
    prior = [load_cache('kummer-source-tangents-status.json', 'hbl-kummer-tangent-strict-*', '',
                        'compiled_source_sha256', 'kummer_source_tangents_validation.py'),
             load_cache('kummer-prescribed-annulus-status.json', 'hbl-prescribed-annulus-strict-*', 'lib',
                        'compiled_artifact_sha256', 'kummer_prescribed_annulus_validation.py')]
    revisions = {}
    for p in json.loads(Path('lake-manifest.json').read_text())['packages']:
        rev = subprocess.check_output(['git', '-C', '.lake/packages/' + p['name'],
                                       'rev-parse', 'HEAD'], text=True).strip()
        assert rev == p['rev']
        assert all(rev == r['dependency_revisions'][p['name']] for _, r, _, _ in prior)
        revisions[p['name']] = rev
    assert revisions['mathlib'] == 'a98628e16c11f5167f16124105ddce53efa9bfe5'
    report['dependency_revisions'] = revisions
    snapshot = {f: digest(f) for f in SOURCES + [AUDIT]}
    for f in SOURCES + [AUDIT]:
        code = mask_comments_and_strings(Path(f).read_text())
        assert len(re.findall(r'^(?:theorem|lemma) ', code, re.M)) == int(f != AUDIT), f
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', code), f
        assert not re.search(r'set_option\s+(?:linter\.|warningAsError\s+false)', code), f
    audit = Path(AUDIT).read_text()
    assert re.findall(r'^#check @(\S+)', audit, re.M) == NAMES
    assert re.findall(r'^#print axioms (\S+)', audit, re.M) == NAMES
    definitions = re.findall(r'^#print (?!axioms )(\S+)', audit, re.M)
    reached = set()
    def visit(f):
        if f in reached:
            return
        reached.add(f)
        for m in re.findall(r'^import (\S+)', Path(f).read_text(), re.M):
            nxt = m.replace('.', '/') + '.lean'
            if nxt in SOURCES:
                visit(nxt)
    visit(SOURCES[-1])
    assert reached == set(SOURCES), reached
    lib = EVIDENCE / 'lib'
    (lib / 'HBL').mkdir(parents=True)
    # Reuse only verified old blocks. Historical flat foundations were restored
    # by the normal pinned build; that build is not a whole-paper strict audit.
    for entry in Path('.lake/build/lib/lean/HBL').iterdir():
        if entry.name != 'KummerPrescribedAnnulus':
            old = prior[0][2] / 'HBL' / entry.name
            chosen = old if old.exists() else entry
            (lib / 'HBL' / entry.name).symlink_to(chosen.resolve(), target_is_directory=chosen.is_dir())
    target_dir = lib / 'HBL/KummerPrescribedAnnulus'
    target_dir.mkdir()
    for f in prior[1][1]['compiled_artifact_sha256']:
        artifact = prior[1][2] / Path(f).with_suffix('.olean')
        (target_dir / artifact.name).symlink_to(artifact.resolve())
    env = os.environ.copy()
    env['LEAN_PATH'] = str(lib) + os.pathsep + subprocess.check_output(
        ['lake', 'env', 'printenv', 'LEAN_PATH'], text=True).strip()
    artifacts = {}
    for f in SOURCES:
        target = lib / Path(f).with_suffix('.olean')
        run(['lean', '--trust=0', '-DwarningAsError=true', '-o', str(target), f], Path(f).stem + '.log', env)
        artifacts[f] = target
    compiled = {f: digest(p) for f, p in artifacts.items()}
    output = run(['lean', '--trust=0', '-DwarningAsError=true', AUDIT], 'audit.txt', env)
    assert not any(s in output for s in ['sorryAx', '⋯', '…'])
    assert all(re.search(r'\bdef ' + re.escape(n) + r'\b', output) for n in definitions)
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output, re.S)
    assert [n for n, _ in found] == NAMES, found
    report['axioms'] = {}
    for n, axioms in found:
        used = {re.sub(r'\.\{[^}]*\}$', '', x.strip()) for x in axioms.split(',') if x.strip()}
        assert used <= ALLOWED, used
        report['axioms'][n] = sorted(used)
    assert snapshot == {f: digest(f) for f in SOURCES + [AUDIT]}
    assert compiled == {f: digest(p) for f, p in artifacts.items()}
    for _, r, cache, key in prior:
        assert all(digest(f) == h for f, h in r['source_sha256'].items())
        assert all(digest(cache / Path(f).with_suffix('.olean')) == h for f, h in r[key].items())
    evidence = Path('verification/kummer-compact-prescribed-types-and-axioms.txt.gz')
    evidence.write_bytes(gzip.compress(output.encode(), mtime=0))
    assert gzip.decompress(evidence.read_bytes()) == output.encode()
    report.update(validation_passed=True, one_theorem_per_file=True,
                  isolated_fresh_new_source_compilation=True, audit_exit_code=0,
                  reused_strict_certificates=[str(p) for p, _, _, _ in prior],
                  reused_strict_artifact_count=sum(len(r[k]) for _, r, _, k in prior),
                  reused_source_and_artifact_hashes_verified=True,
                  strict_source_exit_codes={f: 0 for f in SOURCES}, source_sha256=snapshot,
                  compiled_artifact_sha256=compiled, audited_definition_bodies=definitions,
                  audited_structure_constructor='HBL.Profile.Kummer.LocalKummerPair.mk',
                  complete_type_output_artifact=str(evidence), complete_type_output_bytes=len(output.encode()),
                  complete_type_output_sha256=hashlib.sha256(output.encode()).hexdigest(),
                  compressed_output_sha256=digest(evidence),
                  scope='Input annulus and input compact real parameter set: one uniform basis bound, inverse operator bound, source stability and equation-residual estimate. Endpoint normalization is the center-normalized actual basis at each parameter. Parameter derivatives, manuscript outgoing-basis matching and actual nonlinear Hartree residual cancellation remain open.')
except Exception as exc:
    report['error'] = repr(exc)
Path('verification/kummer-compact-prescribed-status.json').write_text(
    json.dumps(report, indent=2, ensure_ascii=False) + '\n')
print(json.dumps(report, indent=2, ensure_ascii=False))
raise SystemExit(0 if report['validation_passed'] else 1)
