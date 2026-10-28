#!/usr/bin/env python3
"""Strict complete-source difference audit; do not infer manuscript closure."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

BASE = '30c9b88b84d01af7008ad2e9bf09a918cbc83bc6'
TARGET = 'HartreeFullFirstOrderDifference'
NAMES = ['hartree_first_order_difference_noncompact']


def main():
    Path('evidence').mkdir(exist_ok=True)
    report = {
        'source_commit': os.environ['GITHUB_SHA'], 'run_id': os.environ['GITHUB_RUN_ID'],
        'baseline': BASE, 'validation_passed': False,
        'main_theorem_closed': False, 'new_original_environments_verified': 0,
        'full_paper_percentage_recertified': False,
        'boundary': 'One full terminal: actual seventh-order Hartree source differences and their full spatial differentials are L2 with explicit coefficients independent of the increment size d; the weak derivative identity is also derived. Both fields are C1, L4 and bounded with L2/bounded differentials; only the increment is L2. The extra small-ball factor for the Taylor remainder, higher Sobolev closure and actual constrained evolution are NOT asserted.',
        'strict_targets': {},
    }
    errors = {}

    def run(cmd, log):
        try:
            p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
            out, status = p.stdout, p.returncode
        except subprocess.TimeoutExpired as exc:
            out = exc.stdout or ''
            if isinstance(out, bytes): out = out.decode(errors='replace')
            out += '\nVALIDATOR subprocess timeout (600 seconds)\n'
            status = 124
        Path('evidence/' + log).write_text(out)
        blocks, active = [], []
        for line in out.splitlines():
            if re.match(r'(?:error|warning|info): ', line) or re.match(r'HBL/.*: (?:error|warning):', line) or line.startswith('trace:') or ' Built ' in line or ' Building ' in line:
                if active: blocks.append('\n'.join(active)); active = []
                if ('error:' in line or 'warning:' in line) and TARGET in line: active = [line]
            elif active: active.append(line)
        if active: blocks.append('\n'.join(active))
        if status and not blocks: blocks = [out[-30000:]]
        if blocks: errors[log] = '\n\n'.join(blocks)
        return status, out

    try:
        preserved = []
        for name in subprocess.check_output(['git','ls-tree','-r','--name-only',BASE], text=True).splitlines():
            if name.endswith('.lean'):
                assert Path(name).read_bytes() == subprocess.check_output(['git','show',BASE+':'+name]), name
                preserved.append(name)
        report['baseline_Lean_sources_byte_identical'] = len(preserved)
        removed = []
        for path in Path('.lake/build').rglob(TARGET+'.*'):
            if path.is_file(): removed.append(str(path)); path.unlink()
        report['target_cached_files_removed'] = removed
        src = Path('HBL/'+TARGET+'.lean').read_text()
        assert re.findall(r'^(?:def|theorem) (\w+)', src, re.M) == NAMES
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', src)
        assert not re.search(r'set_option\s+(?:linter\.|warningAsError\s+false)', src)
        report['new_source_sha256'] = hashlib.sha256(src.encode()).hexdigest()
        build, _ = run(['lake','build','HBL.'+TARGET], 'full-difference-build.log')
        report['build_exit'] = build
        if build == 0:
            sys.path.insert(0,'verification')
            from quartic_gradient_validation import GROUPS
            groups = dict(GROUPS)
            groups['HartreeLocalCutoff'] = ('HBL.RegularRadiation.LocalCutoff.', ['potential_hasFDerivAt_noncompact','quarticPotential_hasFDerivAt_noncompact'])
            groups['HartreeFirstOrderSource'] = ('HBL.RegularRadiation.FirstOrderSource.', ['hartree_differential_noncompact','hartree_first_order_source_noncompact','hartree_weak_first_order_source'])
            groups['HartreeGradientDifference'] = ('HBL.RegularRadiation.GradientDifference.', ['quarticDensity_fderiv_difference','quartic_potential_first_order_difference'])
            groups[TARGET] = ('HBL.RegularRadiation.FullFirstOrderDifference.', NAMES)
            all_ok = True
            for module,(prefix,short) in groups.items():
                code = Path('HBL/'+module+'.lean').read_text()
                assert re.findall(r'^(?:def|theorem) (\w+)',code,re.M) == short,module
                names = [prefix+n for n in short]
                strict,_ = run(['lake','env','lean','--trust=0','-DwarningAsError=true','HBL/'+module+'.lean'],module+'-strict.log')
                entry = {'strict_exit':strict,'audit_passed':False,'source_sha256':hashlib.sha256(code.encode()).hexdigest(),'declarations':names}
                if strict == 0:
                    audit = 'import HBL.'+module+'\nset_option pp.all true\nset_option pp.maxSteps 10000000\nset_option maxRecDepth 1000000\n'
                    audit += '\n'.join('#check @'+n for n in names)+'\n'
                    audit += '\n'.join('set_option pp.all false in\n#print axioms '+n for n in names)+'\n'
                    path = Path('evidence/'+module+'Audit.lean'); path.write_text(audit)
                    ae,out = run(['lake','env','lean','--trust=0','-DwarningAsError=true',str(path)],module+'-types-and-axioms.txt')
                    found = [(m.group(1),m.group(2) or '') for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",out,re.S)]
                    ok = ae==0 and [n for n,_ in found]==names and not any(x in out for x in ['sorryAx','⋯','...'])
                    ok = ok and all({x.strip() for x in axs.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'} for _,axs in found)
                    entry['audit_passed']=bool(ok)
                    entry['axioms']={n:[x.strip() for x in axs.split(',') if x.strip()] for n,axs in found}
                all_ok = all_ok and entry['audit_passed']
                report['strict_targets'][module]=entry
            if all_ok:
                from proofchain_scan import ROOTS
                regression,_ = run(['lake','build','HBL','HBL.SpectralBridgeTypes',*ROOTS], 'retained-regression.log')
                report['retained_roots_build_exit']=regression
                report['retained_component_roots']=len(ROOTS)
                report['validation_passed']=regression==0
                report['strict_named_declarations']=sum(len(v[1]) for v in groups.values())
                report['new_public_theorems']=len(NAMES)
                report['trust_zero']=True
                report['warning_as_error']=True
                report['prior_proof_sources_unchanged']=True
    except Exception as exc:
        errors['validation-exception']=repr(exc)
    finally:
        for folder in ['verification','evidence']:
            Path(folder+'/full-difference-current-status.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
            Path(folder+'/full-difference-current-errors.json').write_text(json.dumps(errors,ensure_ascii=False,indent=2)+'\n')
        print(json.dumps(report,ensure_ascii=False,indent=2))
        print(json.dumps(errors,ensure_ascii=False,indent=2))

if __name__=='__main__':
    main()
