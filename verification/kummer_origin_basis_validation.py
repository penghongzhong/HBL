#!/usr/bin/env python3
"""Fresh strict audit of the origin-normalized actual Kummer basis.
Only three prior strict finite-IVP sources are rebuilt; historical flat imports
come from the ordinary pinned build. This is not a whole-repository strict audit.
"""
from pathlib import Path
import gzip
import hashlib
import json
import os
import re
import subprocess
import tempfile
from proofchain_scan import mask_comments_and_strings

BLOCK = 'HBL/KummerOriginBasis/'
SOURCES = [BLOCK + n + '.lean' for n in [
    'Definitions', 'RegularIVP', 'Existence', 'Wronskian', 'PhysicalJets',
    'Normalization', 'UniformBound', 'PhysicalWronskian', 'CertificateDefinitions',
    'AnnulusBound', 'Uniqueness', 'AsymptoticBound', 'CompactBasis']]
FOUNDATIONS = ['HBL/KummerPrescribedAnnulus/' + n + '.lean'
              for n in ['Clip', 'LinearIVP', 'PhysicalDefinitions']]
AUDIT = BLOCK + 'OriginBasisAudit.lean'
NAMES = ['HBL.Profile.Kummer.' + n for n in [
    'clipRealVector_properties', 'exists_linear_ivp_on_prescribed_interval',
    'exists_origin_kummer_prescribed_ivp', 'exists_origin_kummer_pair',
    'origin_kummer_wronskian_exact', 'origin_kummer_physical_jets',
    'origin_kummer_normalization', 'origin_kummer_pair_bound',
    'origin_physical_wronskian_exact', 'origin_kummer_annulus_bound',
    'origin_kummer_pair_unique', 'origin_kummer_asymptotic_bound',
    'exists_compact_origin_kummer_basis']]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
EVIDENCE = Path(tempfile.mkdtemp(prefix='hbl-origin-basis-strict-'))
report = dict(validation_passed=False, new_supporting_theorems=11,
              target_original_environment='prop:one-layer-stage3',
              target_original_environment_closed=False,
              newly_accepted_original_environments=0,
              strict_original_environment_count='9/21', main_PDE_theorem_closed=False)


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


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
    prior = json.loads(Path('verification/kummer-prescribed-annulus-status.json').read_text())
    assert prior['validation_passed']
    assert all(digest(f) == prior['source_sha256'][f] for f in FOUNDATIONS)
    revisions = {}
    for p in json.loads(Path('lake-manifest.json').read_text())['packages']:
        rev = subprocess.check_output(['git', '-C', '.lake/packages/' + p['name'],
                                       'rev-parse', 'HEAD'], text=True).strip()
        assert rev == p['rev'] == prior['dependency_revisions'][p['name']]
        revisions[p['name']] = rev
    assert revisions['mathlib'] == 'a98628e16c11f5167f16124105ddce53efa9bfe5'
    report['dependency_revisions'] = revisions
    snapshot = {f: digest(f) for f in FOUNDATIONS + SOURCES + [AUDIT]}
    for f in FOUNDATIONS + SOURCES + [AUDIT]:
        code = mask_comments_and_strings(Path(f).read_text())
        assert len(re.findall(r'^(?:theorem|lemma) ', code, re.M)) <= 1, f
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', code), f
        assert not re.search(r'set_option\s+(?:linter\.|warningAsError\s+false)', code), f
    assert sum(len(re.findall(r'^(?:theorem|lemma) ', mask_comments_and_strings(Path(f).read_text()), re.M))
               for f in SOURCES) == 11
    audit = Path(AUDIT).read_text()
    assert re.findall(r'^#check @(\S+)', audit, re.M) == NAMES
    assert re.findall(r'^#print axioms (\S+)', audit, re.M) == NAMES
    assert '#check HBL.Profile.Kummer.OriginKummerPair.mk\n' in audit
    definitions = re.findall(r'^#print (?!axioms )(\S+)', audit, re.M)
    reached = set()
    def visit(f):
        if f in reached:
            return
        reached.add(f)
        for m in re.findall(r'^import (\S+)', Path(f).read_text(), re.M):
            nxt = m.replace('.', '/') + '.lean'
            if nxt in SOURCES + FOUNDATIONS:
                visit(nxt)
    visit(SOURCES[-1])
    assert reached == set(SOURCES + FOUNDATIONS), reached
    lib = EVIDENCE / 'lib'
    (lib / 'HBL').mkdir(parents=True)
    for entry in Path('.lake/build/lib/lean/HBL').iterdir():
        if entry.name not in ['KummerOriginBasis', 'KummerPrescribedAnnulus']:
            (lib / 'HBL' / entry.name).symlink_to(entry.resolve(), target_is_directory=entry.is_dir())
    env = os.environ.copy()
    env['LEAN_PATH'] = str(lib) + os.pathsep + subprocess.check_output(
        ['lake', 'env', 'printenv', 'LEAN_PATH'], text=True).strip()
    artifacts = {}
    for f in FOUNDATIONS + SOURCES:
        for m in re.findall(r'^import (\S+)', Path(f).read_text(), re.M):
            nxt = m.replace('.', '/') + '.lean'
            if nxt in SOURCES + FOUNDATIONS:
                assert nxt in artifacts, (f, 'dependency not freshly compiled', nxt)
        target = lib / Path(f).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        run(['lean', '--trust=0', '-DwarningAsError=true', '-o', str(target), f],
            str(Path(f).parent.name) + '-' + Path(f).stem + '.log', env)
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
    assert snapshot == {f: digest(f) for f in snapshot}
    assert compiled == {f: digest(p) for f, p in artifacts.items()}
    evidence = Path('verification/kummer-origin-basis-types-and-axioms.txt.gz')
    evidence.write_bytes(gzip.compress(output.encode(), mtime=0))
    assert gzip.decompress(evidence.read_bytes()) == output.encode()
    report.update(validation_passed=True, one_theorem_per_file=True,
                  isolated_fresh_source_compilation=True, audit_exit_code=0,
                  rebuilt_prior_strict_sources=FOUNDATIONS,
                  prior_source_hashes_verified=True,
                  strict_source_exit_codes={f: 0 for f in FOUNDATIONS + SOURCES},
                  source_sha256=snapshot, compiled_artifact_sha256=compiled,
                  audited_definition_bodies=definitions,
                  audited_structure_constructor='HBL.Profile.Kummer.OriginKummerPair.mk',
                  complete_type_output_artifact=str(evidence), complete_type_output_bytes=len(output.encode()),
                  complete_type_output_sha256=hashlib.sha256(output.encode()).hexdigest(),
                  compressed_output_sha256=digest(evidence),
                  scope='Actual origin-normalized singular/regular Kummer basis on any input positive annulus, for every parameter in an input compact real set: physical C2 equations, exact manuscript Wronskian with constant one, origin limits, unique regularized IVPs, common C1/inverse-Wronskian bounds and quantitative Phi=1/r+O(r), Psi=1+O(r^2) bounds. No derivatives in parameters, outgoing Green operator in this basis, weighted overlap, full Frobenius expansion or actual nonlinear Hartree residual cancellation is claimed.')
except Exception as exc:
    report['error'] = repr(exc)
Path('verification/kummer-origin-basis-status.json').write_text(
    json.dumps(report, indent=2, ensure_ascii=False) + '\n')
print(json.dumps(report, indent=2, ensure_ascii=False))
raise SystemExit(0 if report['validation_passed'] else 1)
