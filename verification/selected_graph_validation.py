#!/usr/bin/env python3
"""Reuse actual HBL terminals; separate kernel checks from manuscript closure."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

BASE = '6137fcc06efe539f70f4a2992d3c4cd665d718f7'
TARGET = 'SelectedFixedPointC1'
GROUPS = {
    'ParametricFixedPointC1': ('HBL.MainBackward.', [
        'id_sub_isInvertible_of_norm_lt_one', 'contracting_fixed_point_has_C1_local_graph']),
    'MainRateSelection': ('HBL.MainBackward.', [
        'selectedPhysicalRate', 'selectedPhysicalRate_contDiff', 'selectedPhysicalRate_eq_two_iff']),
    TARGET: ('HBL.MainBackward.', [
        'selected_local_fixedPoint_contDiffAt', 'selected_fixedPoint_shooting_data_rate_C1']),
}


def main():
    Path('evidence').mkdir(exist_ok=True)
    report = {
        'source_commit': os.environ['GITHUB_SHA'],
        'run_id': os.environ['GITHUB_RUN_ID'],
        'baseline': BASE, 'validation_passed': False,
        'main_theorem_closed': False,
        'new_original_environments_verified': 0,
        'full_paper_percentage_recertified': False,
        'strict_targets': {},
        'reuse': ['ParametricFixedPointC1: existing implicit-function proof and invertibility',
                 'MainRateSelection: physical rate and its C1 dependence',
                 'existing selected solution family: no second fixed-point construction'],
        'discharged_calculus_inputs': ['continuity and C1 of the selected solution are conclusions',
            'I-D state-partial formula is derived',
            'state derivative norm less than one follows from local contraction',
            'implicit graph is identified with the previously selected fixed point by uniqueness'],
        'remaining_physical_obligations': [
            'construct the actual constrained Hartree evolution in compatible source and domain spaces',
            'prove local C1 of the untruncated physical joint map, including high-regularity remainder estimates',
            'construct the actual fixed-point family and its interior neighborhood uniformly in parameters',
            'prove the physical reconstruction and inverse-coordinate chart hypotheses',
            'assemble every original main-theorem quantifier, orbit, rate and nonextension conclusion'],
        'counting_rule': 'Current module/type checks and historical registered environments are NOT an unconditional 21/21 paper certificate.',
    }
    errors = {}

    def run(cmd, log):
        try:
            proc = subprocess.run(cmd, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=600)
            status, out = proc.returncode, proc.stdout
        except subprocess.TimeoutExpired as exc:
            status, out = 124, exc.stdout or ''
            if isinstance(out, bytes): out = out.decode(errors='replace')
            out += '\nVALIDATOR subprocess timeout\n'
        Path('evidence/' + log).write_text(out)
        if status:
            errors[log] = out[-30000:]
        return status, out

    def audit(module, prefix, short):
        src = Path('HBL/' + module + '.lean').read_text()
        assert re.findall(r'^(?:def|theorem) (\w+)', src, re.M) == short, module
        names = [prefix + n for n in short]
        strict, _ = run(['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true',
                         'HBL/' + module + '.lean'], module + '-strict.log')
        entry = {'strict_exit': strict, 'audit_passed': False,
                 'source_sha256': hashlib.sha256(src.encode()).hexdigest(),
                 'declarations': names}
        if strict == 0:
            ae, out, found = check_names(['HBL.' + module], names, module)
            entry['audit_passed'] = ae == 0
            entry['axioms'] = {n: [x.strip() for x in a.split(',') if x.strip()] for n, a in found}
        return entry

    def check_names(imports, names, stem):
        text = '\n'.join('import ' + n for n in imports) + '\n'
        text += 'set_option pp.all true\nset_option pp.maxSteps 10000000\nset_option maxRecDepth 1000000\n'
        text += '\n'.join('#check @' + n for n in names) + '\n'
        text += '\n'.join('set_option pp.all false in\n#print axioms ' + n for n in names) + '\n'
        path = Path('evidence/' + stem + 'Audit.lean'); path.write_text(text)
        code, out = run(['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true', str(path)],
                        stem + '-complete-types-and-axioms.txt')
        found = [(m.group(1), m.group(2) or '') for m in re.finditer(
            r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", out, re.S)]
        good = (code == 0 and [n for n, _ in found] == names and
                not any(bad in out for bad in ['sorryAx', '⋯', '...']) and
                all({x.strip() for x in a.split(',') if x.strip()} <=
                    {'propext', 'Classical.choice', 'Quot.sound'} for _, a in found))
        if not good:
            errors[stem + '-inventory'] = 'Full-type or exact axiom inventory failed. Compiler exit: ' + str(code)
        return (0 if good else 1), out, found

    try:
        preserved = []
        for name in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE], text=True).splitlines():
            if name.endswith('.lean'):
                assert Path(name).read_bytes() == subprocess.check_output(['git', 'show', BASE + ':' + name]), name
                preserved.append(name)
        report['baseline_Lean_sources_byte_identical'] = len(preserved)
        src = Path('HBL/' + TARGET + '.lean').read_text()
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', src)
        assert not re.search(r'set_option\s+(?:linter\.|warningAsError\s+false)', src)
        removed = []
        for path in Path('.lake/build').rglob(TARGET + '.*'):
            if path.is_file(): removed.append(str(path)); path.unlink()
        report['target_cached_files_removed'] = removed
        code, _ = run(['lake', 'build', 'HBL.' + TARGET], 'selected-graph-build.log')
        report['build_exit'] = code
        if code == 0:
            all_ok = True
            for module, (prefix, short) in GROUPS.items():
                item = audit(module, prefix, short)
                report['strict_targets'][module] = item
                all_ok = all_ok and item['audit_passed']
            if all_ok:
                sys.path.insert(0, 'verification')
                from proofchain_scan import ROOTS
                rc, _ = run(['lake', 'build', 'HBL', 'HBL.SpectralBridgeTypes', *ROOTS], 'retained-regression.log')
                report['retained_roots_build_exit'] = rc
                report['retained_component_roots'] = len(ROOTS)
                if rc == 0:
                    ledger = json.loads(Path('verification/current-environments-20261026.json').read_text())
                    entries = [e for e in ledger['environments'] if e.get('terminals')]
                    names = list(dict.fromkeys(n for e in entries for n in e['terminals']))
                    lec, _, laf = check_names(['HBL', *ROOTS], names, 'ExistingEnvironmentTerminals')
                    report['registered_environment_terminal_audit_exit'] = lec
                    report['registered_environment_terminal_count'] = len(names)
                    report['registered_environment_groups_checked'] = len(entries)
                    report['registered_environment_scope_preserved_NOT_promoted'] = entries
                    report['registered_environment_axioms'] = {
                        n: [x.strip() for x in a.split(',') if x.strip()] for n, a in laf}
                    report['historical_ledger_not_a_current_21_environment_certificate'] = True
                    report['validation_passed'] = lec == 0
                report['strict_current_declarations'] = sum(len(v[1]) for v in GROUPS.values())
                report['new_public_calculus_terminals'] = 2
                report['trust_zero'] = True
                report['warning_as_error'] = True
    except Exception as exc:
        errors['validation-exception'] = repr(exc)
    finally:
        for directory in ['verification', 'evidence']:
            Path(directory + '/selected-graph-current-status.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
            Path(directory + '/selected-graph-current-errors.json').write_text(json.dumps(errors, ensure_ascii=False, indent=2) + '\n')
        print(json.dumps(report, ensure_ascii=False, indent=2))
        print(json.dumps(errors, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()
