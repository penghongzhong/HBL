#!/usr/bin/env python3
"""Strict kernel/type audit for the actual differentiated density remainder."""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys

BASE = 'c7e0e3458f8adffd764e5793b591f2f32c6afd16'
TARGET = 'HartreeDensityRemainderGradient'
GROUPS = {
 'HartreeDensitySourceBounds': ('HBL.RegularRadiation.PhysicalExpansion.', ['densityQuadraticConstant','densityLinear_source_integrable','densityRemainder_source_bound','densityRemainder_small_ball_bound','physical_hartree_expansion_from_function_bounds']),
 'HartreeLocalCutoff': ('HBL.RegularRadiation.LocalCutoff.', ['potential_hasFDerivAt_noncompact','quarticPotential_hasFDerivAt_noncompact']),
 TARGET: ('HBL.RegularRadiation.PhysicalExpansion.', ['densityGradientQuadraticConstant','densityRemainder_contDiff','densityRemainder_fderiv_apply','densityRemainder_fderiv_norm_le','densityRemainder_gradient_quadratic','densityRemainder_potential_gradient_quadratic']),
}

def main():
 Path('evidence').mkdir(exist_ok=True)
 report = {'source_commit':os.environ['GITHUB_SHA'],'run_id':os.environ['GITHUB_RUN_ID'],
  'baseline':BASE,'validation_passed':False,'main_theorem_closed':False,
  'new_original_environments_verified':0,'full_paper_percentage_recertified':False,
  'boundary':'Native spatial differentiation of the actual quadratic quartic-density remainder. Its gradient mass and supremum, and the actual noncompact gradient potential, are O(r^2) on the mixed first-order perturbation ball. Real background C1/bounded/bounded derivative; no background L2 or L4. This is not the full seventh-order remainder difference, high Sobolev closure, actual constrained evolution or main blow-up theorem.',
  'strict_targets':{}}
 errors={}
 def run(cmd,log):
  try:
   p=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=600)
   status,out=p.returncode,p.stdout
  except subprocess.TimeoutExpired as exc:
   status,out=124,exc.stdout or ''
   if isinstance(out,bytes): out=out.decode(errors='replace')
   out+='\nVALIDATOR timeout\n'
  Path('evidence/'+log).write_text(out)
  if status:
   blocks=[]; active=[]
   for line in out.splitlines():
    if re.match(r'(?:error|warning|info): |HBL/.*: (?:error|warning):|trace:|[✖⚠ℹ✔]',line):
     if active: blocks.append('\n'.join(active)); active=[]
     if ('error:' in line or 'warning:' in line) and TARGET in line: active=[line]
    elif active: active.append(line)
   if active: blocks.append('\n'.join(active))
   errors[log]='\n\n'.join(blocks) if blocks else out[-12000:]
  return status,out
 try:
  preserved=[]
  for name in subprocess.check_output(['git','ls-tree','-r','--name-only',BASE],text=True).splitlines():
   if name.endswith('.lean'):
    assert Path(name).read_bytes()==subprocess.check_output(['git','show',BASE+':'+name]),name
    preserved.append(name)
  report['baseline_Lean_sources_byte_identical']=len(preserved)
  src=Path('HBL/'+TARGET+'.lean').read_text()
  assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',src)
  assert not re.search(r'set_option\s+(?:linter\.|warningAsError\s+false)',src)
  removed=[]
  for path in Path('.lake/build').rglob(TARGET+'.*'):
   if path.is_file(): removed.append(str(path)); path.unlink()
  report['target_cached_files_removed']=removed
  build,_=run(['lake','build','HBL.'+TARGET],'density-remainder-gradient-build.log')
  report['build_exit']=build
  if build==0:
   ok=True
   for module,(prefix,short) in GROUPS.items():
    text=Path('HBL/'+module+'.lean').read_text()
    assert re.findall(r'^(?:def|theorem) (\w+)',text,re.M)==short,module
    names=[prefix+n for n in short]
    strict,_=run(['lake','env','lean','--trust=0','-DwarningAsError=true','HBL/'+module+'.lean'],module+'-strict.log')
    entry={'strict_exit':strict,'audit_passed':False,'source_sha256':hashlib.sha256(text.encode()).hexdigest(),'declarations':names}
    if strict==0:
     audit='import HBL.'+module+'\nset_option pp.all true\nset_option pp.maxSteps 10000000\nset_option maxRecDepth 1000000\n'
     audit+='\n'.join('#check @'+n for n in names)+'\n'
     audit+='\n'.join('set_option pp.all false in\n#print axioms '+n for n in names)+'\n'
     path=Path('evidence/'+module+'Audit.lean'); path.write_text(audit)
     ae,out=run(['lake','env','lean','--trust=0','-DwarningAsError=true',str(path)],module+'-complete-types-and-axioms.txt')
     found=[(m.group(1),m.group(2) or '') for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",out,re.S)]
     passed=ae==0 and [n for n,_ in found]==names and not any(x in out for x in ['sorryAx','⋯','...'])
     passed=passed and all({x.strip() for x in axs.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'} for _,axs in found)
     entry['audit_passed']=bool(passed)
     entry['axioms']={n:[x.strip() for x in axs.split(',') if x.strip()] for n,axs in found}
    report['strict_targets'][module]=entry
    ok=ok and entry['audit_passed']
   if ok:
    sys.path.insert(0,'verification')
    from proofchain_scan import ROOTS
    regression,_=run(['lake','build','HBL','HBL.SpectralBridgeTypes','HBL.SelectedFixedPointC1','HBL.HartreeFullFirstOrderDifference',*ROOTS],'retained-regression.log')
    report['retained_roots_build_exit']=regression
    report['retained_component_roots']=len(ROOTS)
    report['strict_named_declarations']=sum(len(v[1]) for v in GROUPS.values())
    report['new_public_theorems']=5
    report['trust_zero']=True; report['warning_as_error']=True
    report['validation_passed']=regression==0
 except Exception as exc:
  errors['validation-exception']=repr(exc)
 finally:
  for directory in ['verification','evidence']:
   Path(directory+'/density-remainder-gradient-current-status.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
   Path(directory+'/density-remainder-gradient-current-errors.json').write_text(json.dumps(errors,ensure_ascii=False,indent=2)+'\n')
  print(json.dumps(report,ensure_ascii=False,indent=2))
  print(json.dumps(errors,ensure_ascii=False,indent=2))

if __name__=='__main__': main()
