#!/usr/bin/env python3
"""Strictly check the complete physical first-order source, preserving old proofs."""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys
BASE = '53274ac98628f02ee0a69d36223c7677f663802c'
TARGET = 'HartreeFirstOrderSource'
NAMES = ['hartree_differential_noncompact', 'hartree_first_order_source_noncompact', 'hartree_weak_first_order_source']

def main():
    Path('evidence').mkdir(exist_ok=True)
    report = {'source_commit': os.environ['GITHUB_SHA'], 'run_id': os.environ['GITHUB_RUN_ID'],
        'baseline': BASE, 'validation_passed': False, 'main_theorem_closed': False,
        'new_original_environments_verified': 0, 'full_paper_percentage_recertified': False,
        'boundary': 'The complete nonlinearity and its first differential are proved L2, and the weak-derivative test identity is derived with all product integrability conditions discharged. The input is a C1 field in L4 and bounded, with L2 and bounded differential. No field L2, support or approximation hypothesis is introduced. Identification with higher Bessel Sobolev spaces, higher-order and Taylor-remainder difference estimates, and the actual constrained evolution remain separate obligations.',
        'strict_targets': {}}
    errors = {}
    def run(cmd, log):
        p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        Path('evidence/'+log).write_text(p.stdout)
        if p.returncode:
            lines=p.stdout.splitlines(); hits=[]
            for i,line in enumerate(lines):
                if 'error:' in line or re.search(r'\.lean:\d+:\d+: (?:error|warning):',line):
                    hits.append('\n'.join(lines[i:i+65]))
            errors[log]='\n\n'.join(hits) if hits else p.stdout[-22000:]
        return p.returncode, p.stdout
    try:
        preserved=[]
        for name in subprocess.check_output(['git','ls-tree','-r','--name-only',BASE],text=True).splitlines():
            if name.endswith('.lean'):
                assert Path(name).read_bytes()==subprocess.check_output(['git','show',BASE+':'+name]),name
                preserved.append(name)
        report['baseline_Lean_sources_byte_identical']=len(preserved)
        removed=[]
        for path in Path('.lake/build').rglob(TARGET+'.*'):
            if path.is_file(): removed.append(str(path)); path.unlink()
        report['new_target_cached_files_removed']=removed
        src=Path('HBL/'+TARGET+'.lean').read_text()
        assert re.findall(r'^(?:def|theorem) (\w+)',src,re.M)==NAMES
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',src)
        report['new_source_sha256']=hashlib.sha256(src.encode()).hexdigest()
        build,_=run(['lake','build','HBL.'+TARGET],'first-order-build.log')
        report['build_exit']=build
        if build==0:
            sys.path.insert(0,'verification')
            from quartic_gradient_validation import GROUPS
            groups=dict(GROUPS)
            groups['HartreeLocalCutoff']=('HBL.RegularRadiation.LocalCutoff.', ['potential_hasFDerivAt_noncompact','quarticPotential_hasFDerivAt_noncompact'])
            groups[TARGET]=('HBL.RegularRadiation.FirstOrderSource.', NAMES)
            all_ok=True
            for module,(prefix,short) in groups.items():
                code=Path('HBL/'+module+'.lean').read_text()
                assert re.findall(r'^(?:def|theorem) (\w+)',code,re.M)==short,module
                names=[prefix+n for n in short]
                strict,_=run(['lake','env','lean','--trust=0','-DwarningAsError=true','HBL/'+module+'.lean'],module+'-strict.log')
                entry={'strict_exit':strict,'audit_passed':False,'source_sha256':hashlib.sha256(code.encode()).hexdigest(),'declarations':names}
                if strict==0:
                    audit='import HBL.'+module+'\nset_option pp.all true\nset_option pp.maxSteps 10000000\nset_option maxRecDepth 1000000\n'
                    audit+='\n'.join('#check @'+n for n in names)+'\n'
                    audit+='\n'.join('set_option pp.all false in\n#print axioms '+n for n in names)+'\n'
                    path=Path('evidence/'+module+'Audit.lean');path.write_text(audit)
                    ae,out=run(['lake','env','lean','--trust=0','-DwarningAsError=true',str(path)],module+'-types-and-axioms.txt')
                    found=[(m.group(1),m.group(2) or '') for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",out,re.S)]
                    ok=ae==0 and [n for n,_ in found]==names and not any(x in out for x in ['sorryAx','⋯','...'])
                    ok=ok and all({x.strip() for x in a.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'} for _,a in found)
                    entry['audit_passed']=bool(ok)
                    entry['axioms']={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in found}
                all_ok=all_ok and entry['audit_passed']
                report['strict_targets'][module]=entry
            if all_ok:
                from proofchain_scan import ROOTS
                regression,_=run(['lake','build','HBL','HBL.SpectralBridgeTypes',*ROOTS],'retained-regression.log')
                report['retained_roots_build_exit']=regression
                report['validation_passed']=regression==0
                report['strict_named_declarations']=sum(len(v[1]) for v in groups.values())
                report['new_public_theorems']=len(NAMES)
                report['trust_zero']=True
                report['warning_as_error']=True
    except Exception as exc:
        errors['validation-exception']=repr(exc)
    finally:
        for folder in ['verification','evidence']:
            Path(folder+'/first-order-current-status.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
            Path(folder+'/first-order-current-errors.json').write_text(json.dumps(errors,ensure_ascii=False,indent=2)+'\n')
        print(json.dumps(report,ensure_ascii=False,indent=2))
        print(json.dumps(errors,ensure_ascii=False,indent=2))
if __name__=='__main__':
    main()
