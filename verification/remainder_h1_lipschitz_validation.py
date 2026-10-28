#!/usr/bin/env python3
"""Strict physical H1 Lipschitz and complete original-environment validation."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

BASE = '3614e05c4525ac5b8d5fefea063eae16882dbed3'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
GROUPS = {
    'HartreeRemainderInterpolation': ('HBL.RegularRadiation.PhysicalInterpolation.', [
        'interpolationCoefficients', 'remainderWeight', 'interpolationBound',
        'remainderWeight_bound', 'sampleField', 'sample_kernel_integrable',
        'physical_remainder_interpolation']),
    'HartreeFirstOrderSource': ('HBL.RegularRadiation.FirstOrderSource.', [
        'hartree_differential_noncompact', 'hartree_first_order_source_noncompact',
        'hartree_weak_first_order_source']),
    'HartreeFullFirstOrderDifference': ('HBL.RegularRadiation.FullFirstOrderDifference.', [
        'hartree_first_order_difference_noncompact']),
    'HartreeRemainderFirstOrderQuadratic': ('HBL.RegularRadiation.RemainderFirstOrder.', [
        'eight_L2_combination', 'remainderFirstOrderConstant', 'affine_sample_data',
        'physical_remainder_first_order_quadratic']),
    'HartreeRemainderFirstOrderLipschitz': (
        'HBL.RegularRadiation.RemainderFirstOrderLipschitz.', [
            'remainderFirstOrderLipschitzConstant',
            'physical_remainder_first_order_normalized_difference',
            'FirstOrderBall', 'physical_remainder_first_order_lipschitz']),
    'HartreeRemainderH1Lipschitz': ('HBL.RegularRadiation.RemainderH1.', [
        'mixedFirstOrderNorm', 'physicalH1Norm', 'physical_remainder_h1_lipschitz']),
    'HartreeGraphKernelBounds': ('HBL.RegularRadiation.GraphKernel.', [
        'farKernel', 'potential_graph_bound', 'gradientPotential_graph_bound']),
    'KinematicOriginalEnvironment': ('HBL.Kinematic.', [
        'kinematicRecovery_originalEnvironment_closed']),
}
NEW_MODULES = ['HartreeRemainderFirstOrderLipschitz', 'HartreeRemainderH1Lipschitz',
               'HartreeGraphKernelBounds', 'KinematicOriginalEnvironment']
STATUS = 'remainder-h1-lipschitz-current-status.json'
ERRORS = 'remainder-h1-lipschitz-current-errors.json'


def main():
    sys.path.insert(0, 'verification')
    from proofchain_scan import ROOTS, mask_comments_and_strings
    evidence = Path('evidence/remainder-h1-lipschitz')
    evidence.mkdir(parents=True, exist_ok=True)
    source_commit = os.environ.get('GITHUB_SHA') or subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], text=True).strip()
    report = {
        'source_commit': source_commit,
        'run_id': os.environ.get('GITHUB_RUN_ID', 'local'),
        'baseline': BASE,
        'validation_passed': False,
        'main_theorem_closed': False,
        'new_original_environments_verified': 0,
        'revalidated_original_environments': [],
        'full_paper_percentage_recertified': False,
        'boundary': (
            'The actual seventh-order Hartree remainder is locally Lipschitz from the '
            'mixed first-order X ball to classical Cartesian H1, including the zero '
            'increment and the weak derivative identities. All source samples and '
            'their bounds are derived from the original fields. The background is '
            'real C1, L4 and bounded, with bounded/L2 differential; background L2 '
            'is not assumed. The constrained propagator, high Sobolev local flow, '
            'physical reconstruction and full main theorem remain unconstructed. '
            'This mixed X is not the manuscript homogeneous H1/intersect H25/16 '
            'graph space; no embedding of that graph space into X is claimed. '
            'Two further actual kernel bounds use density Linfty/intersect L3/2 '
            'and differential L1/intersect L25/8; they do not yet identify the '
            'non-L1 density derivative or supply the homogeneous Sobolev bridge. '
            'The synchronized-slice original environment is revalidated, not added '
            'to the historical denominator.'),
        'strict_targets': {},
    }
    errors = {}

    def run(command, filename, timeout=900):
        try:
            p = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=timeout)
            code, output = p.returncode, p.stdout
        except subprocess.TimeoutExpired as exc:
            code, output = 124, exc.stdout or ''
            if isinstance(output, bytes):
                output = output.decode(errors='replace')
            output += '\nVALIDATOR timeout\n'
        (evidence / filename).write_text(output)
        if code:
            errors[filename] = output[-24000:]
        return code, output

    try:
        compiler, version = run(['lean', '--version'], 'compiler.txt')
        assert compiler == 0 and '4.35.0-rc3' in version, version
        mathlib = subprocess.check_output(
            ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], text=True).strip()
        assert mathlib == 'a98628e16c11f5167f16124105ddce53efa9bfe5', mathlib
        report['compiler_version'] = version.strip()
        report['mathlib_commit'] = mathlib

        preserved = []
        for name in subprocess.check_output(
                ['git', 'ls-tree', '-r', '--name-only', BASE], text=True).splitlines():
            if not name.endswith('.lean'):
                continue
            old = subprocess.check_output(['git', 'show', BASE + ':' + name], text=True)
            expected = old
            if name == 'HBL/HartreeRemainderFirstOrderQuadratic.lean':
                for short in ['eight_L2_combination', 'affine_sample_data']:
                    needle = 'private theorem ' + short
                    assert expected.count(needle) == 1
                    expected = expected.replace(needle, 'theorem ' + short)
            assert Path(name).read_text() == expected, name
            preserved.append(name)
        report['baseline_Lean_sources_preserved'] = len(preserved)
        report['only_baseline_Lean_changes'] = 'Two existing helper proofs made public; proof terms unchanged.'

        for module in GROUPS:
            code = mask_comments_and_strings(Path('HBL/' + module + '.lean').read_text())
            assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', code), module
            assert not re.search(r'set_option\s+(?:linter\.|warningAsError\s+false)', code), module
            actual = re.findall(r'^(?:def|theorem|structure) (\w+)', code, re.M)
            assert actual == GROUPS[module][1], (module, actual)

        removed = []
        for module in NEW_MODULES:
            for path in Path('.lake/build').rglob(module + '.*'):
                if path.is_file():
                    removed.append(str(path))
                    path.unlink()
        report['new_target_cached_files_removed'] = removed
        build, _ = run(['lake', 'build', *['HBL.' + m for m in NEW_MODULES]], 'build.log')
        report['build_exit'] = build
        assert build == 0, 'New target build failed; see build.log.'

        complete_audits = []
        for module, (prefix, short) in GROUPS.items():
            src = Path('HBL/' + module + '.lean').read_text()
            names = [prefix + n for n in short]
            strict, _ = run(['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true',
                             'HBL/' + module + '.lean'], module + '-strict.log')
            entry = {
                'strict_exit': strict,
                'source_sha256': hashlib.sha256(src.encode()).hexdigest(),
                'declarations': names,
                'audit_passed': False,
            }
            report['strict_targets'][module] = entry
            assert strict == 0, module + ' strict recheck failed.'
            audit = ('import HBL.' + module + '\nset_option pp.all true\n'
                     'set_option pp.maxSteps 10000000\n'
                     'set_option maxRecDepth 1000000\n')
            audit += '\n'.join('#check @' + n for n in names) + '\n'
            if module == 'HartreeRemainderFirstOrderLipschitz':
                # Lean's structure printer forcibly hides proof arguments even
                # under pp.all. Check the constructor and each projection instead.
                for field in ['mk', 'value_memLp', 'derivative_memLp', 'value_bound',
                              'derivative_bound', 'value_square_integral',
                              'derivative_square_integral']:
                    audit += '#check @' + prefix + 'FirstOrderBall.' + field + '\n'
                audit += '#print ' + prefix + 'remainderFirstOrderLipschitzConstant\n'
            if module == 'HartreeRemainderH1Lipschitz':
                audit += '#print ' + prefix + 'mixedFirstOrderNorm\n'
                audit += '#print ' + prefix + 'physicalH1Norm\n'
                audit += '#print HBL.RegularRadiation.hartreeNonlinearity\n'
                audit += '#print HBL.RegularRadiation.PhysicalExpansion.remainder\n'
            audit += '\n'.join('set_option pp.all false in\n#print axioms ' + n for n in names) + '\n'
            ap = evidence / (module + 'Audit.lean')
            ap.write_text(audit)
            ae, output = run(['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true', str(ap)],
                             module + '-complete-types-and-axioms.txt')
            found = [(m.group(1), m.group(2) or '') for m in re.finditer(
                r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
                output, re.S)]
            passed = ae == 0 and [n for n, _ in found] == names
            passed = passed and not any(x in output for x in ['sorryAx', '⋯', '…', '...'])
            passed = passed and all(
                {a.strip() for a in axs.split(',') if a.strip()} <= ALLOWED_AXIOMS
                for _, axs in found)
            entry['audit_exit'] = ae
            entry['audit_passed'] = bool(passed)
            entry['complete_type_output_bytes'] = len(output.encode())
            entry['complete_type_output_sha256'] = hashlib.sha256(output.encode()).hexdigest()
            entry['axioms'] = {n: [a.strip() for a in axs.split(',') if a.strip()]
                               for n, axs in found}
            complete_audits.append('MODULE ' + module + '\n' + output)
            assert passed, module + ' complete type / axiom audit failed.'

        regression, _ = run(['lake', 'build', 'HBL', 'HBL.SpectralBridgeTypes',
                             'HBL.SelectedFixedPointC1', *ROOTS], 'retained-regression.log', 1200)
        report['retained_roots_build_exit'] = regression
        report['retained_component_roots'] = len(ROOTS)
        assert regression == 0, 'Retained-chain regression failed.'
        report['strict_named_declarations'] = sum(len(v[1]) for v in GROUPS.values())
        report['trust_zero'] = True
        report['warning_as_error'] = True
        report['revalidated_original_environments'] = ['prop:kinematic-recovery-v2']
        report['validation_passed'] = True
        Path('verification/remainder-h1-complete-types-and-axioms.txt').write_text(
            '\n'.join(complete_audits))
    except Exception as exc:
        errors['validation_exception'] = repr(exc)
    finally:
        for directory in [Path('verification'), evidence]:
            (directory / STATUS).write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
            (directory / ERRORS).write_text(json.dumps(errors, ensure_ascii=False, indent=2) + '\n')
        print(json.dumps(report, ensure_ascii=False, indent=2))
        print(json.dumps(errors, ensure_ascii=False, indent=2))
    return 0 if report['validation_passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
