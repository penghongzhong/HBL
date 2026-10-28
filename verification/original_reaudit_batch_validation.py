#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, subprocess, sys

ALLOWED = {'propext','Classical.choice','Quot.sound'}
TARGETS = [
  ('HBL.FirstModulationLemma','HBL.Modulation.firstManuscriptModulationEnvironment_closed','prop:modulation',[448,464]),
  ('HBL.AffineTailLemmaClosed','HBL.Modulation.AffineTail.secondManuscriptAffineTailEnvironment_closed','lem:affine-charge',[476,490]),
  ('HBL.MonopoleFirstCorrectionCertified','HBL.Modulation.Monopole.monopole_first_correction_certified','thm:Xi-mon-tail',[1072,1101]),
  ('HBL.MonopoleThresholdProjection','HBL.Modulation.Monopole.revisedMonopoleCoreManuscriptEnvironment_closed','prop:profile-cancel-stage2',[1162,1200]),
  ('HBL.UnstableShootingTerminal','HBL.Shooting.revisedUnstableShootingManuscriptEnvironment_closed','prop:shooting-stage4',[3915,3952]),
  ('HBL.TransversalityExact','HBL.Modulation.Transversality.manuscript_transversality_environment_closed','thm:transversality',[4383,4394]),
  ('HBL.HartreeKernelShortRange','HBL.Modulation.AffineTail.kernelShortManuscriptEnvironment_closed','lem:kernel-short',[4888,4902]),
]
EVIDENCE=Path('evidence/original-reaudit-batch')
EVIDENCE.mkdir(parents=True,exist_ok=True)

def run(cmd,name,timeout=1200):
    try:
        p=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
        out=p.stdout; code=p.returncode
    except subprocess.TimeoutExpired as exc:
        code=124; out=exc.stdout or ''
        if isinstance(out,bytes): out=out.decode(errors='replace')
        out+='\nVALIDATOR timeout\n'
    (EVIDENCE/name).write_text(out)
    return code,out

report={
  'source_commit':os.environ.get('GITHUB_SHA','local'),
  'run_id':os.environ.get('GITHUB_RUN_ID','local'),
  'validation_passed':False,
  'strictly_revalidated_original_environments_this_batch':0,
  'labels':[t[2] for t in TARGETS],
  'manuscript_line_windows':{t[2]:t[3] for t in TARGETS},
  'main_theorem_closed':False,
  'full_paper_21_of_21_certified':False,
  'trust_zero':True,
  'warning_as_error':True,
}
errors={}
try:
    c,v=run(['lean','--version'],'compiler.txt',60)
    assert c==0 and '4.35.0-rc3' in v,v
    mh=subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],text=True).strip()
    assert mh=='a98628e16c11f5167f16124105ddce53efa9bfe5',mh
    report['compiler']=v.strip(); report['mathlib_commit']=mh

    modules=[m for m,_,_,_ in TARGETS]
    b,_=run(['lake','build',*modules],'build.log',1200)
    report['build_exit']=b
    assert b==0,'target build failed'

    audit='\n'.join('import '+m for m in modules)+'\n'
    audit+='set_option pp.all true\nset_option pp.maxSteps 10000000\nset_option maxRecDepth 1000000\n'
    audit+='\n'.join('#check @'+n for _,n,_,_ in TARGETS)+'\n'
    audit+='\n'.join('set_option pp.all false in\n#print axioms '+n for _,n,_,_ in TARGETS)+'\n'
    ap=EVIDENCE/'OriginalReauditBatch.lean'; ap.write_text(audit)
    ae,out=run(['lake','env','lean','--trust=0','-DwarningAsError=true',str(ap)],'complete-types-and-axioms.txt',1200)
    report['audit_exit']=ae
    assert ae==0,'strict aggregate audit failed'
    expected=[n for _,n,_,_ in TARGETS]
    found=[(m.group(1),m.group(2) or '') for m in re.finditer(
      r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",out,re.S)]
    assert [n for n,_ in found]==expected,([n for n,_ in found],expected)
    assert 'sorryAx' not in out and '⋯' not in out and '…' not in out and '...' not in out
    ax={}
    for n,raw in found:
        aset={x.strip() for x in raw.split(',') if x.strip()}
        assert aset<=ALLOWED,(n,aset)
        ax[n]=sorted(aset)
    report['axioms']=ax
    report['complete_type_output_bytes']=len(out.encode())
    report['complete_type_output_sha256']=hashlib.sha256(out.encode()).hexdigest()
    report['strictly_revalidated_original_environments_this_batch']=7
    report['validation_passed']=True
except Exception as exc:
    errors['exception']=repr(exc)

(EVIDENCE/'status.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
(EVIDENCE/'errors.json').write_text(json.dumps(errors,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(report,ensure_ascii=False,indent=2))
print(json.dumps(errors,ensure_ascii=False,indent=2))
raise SystemExit(0 if report['validation_passed'] else 1)
