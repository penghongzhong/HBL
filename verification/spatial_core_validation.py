"""Verify the actual spatial Hartree core; do not recertify the PDE theorem."""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys

BASE='4999b1fc43c02841f7eb9b39b5c7f003f0b23655'
MODULE='HartreeSpatialCore'
SOURCE=Path('HBL')/(MODULE+'.lean')
Path('evidence').mkdir(exist_ok=True)
sys.path.insert(0,'verification')
from proofchain_scan import ROOTS, mask_comments_and_strings


def command(args, filename):
    with open('evidence/'+filename,'w') as f:
        p=subprocess.run(args,stdout=f,stderr=subprocess.STDOUT)
    return p.returncode


def diagnostic(filename):
    p=Path('evidence/'+filename)
    if not p.exists(): return ''
    text=re.sub(r'\x1b\[[0-9;]*m','',p.read_text())
    lines=text.splitlines(); chunks=[]
    for i,line in enumerate(lines):
        if re.match(r'(?:error|warning): HBL/HartreeSpatialCore',line) or 'error:' in line and 'evidence/' in line:
            end=i+1
            while end<len(lines) and not re.match(r'(?:error|warning|info|trace):',lines[end]) and not re.match(r'[✔✖⚠ℹ]',lines[end]):
                end+=1
            chunks.append('\n'.join(lines[i:end]))
    return '\n\n'.join(chunks) if chunks else text[-6000:]


def main():
    r={'source_commit':os.environ['GITHUB_SHA'],'run_id':os.environ['GITHUB_RUN_ID'],
       'module':MODULE,'baseline':BASE,'main_theorem_closed':False,
       'new_original_environments_verified':0,'full_paper_percentage_recertified':False,
       'validation_passed':False,'strict_exit':None,'audit_passed':False,
       'retained_roots_build_exit':None,'boundary':'C1 compactly supported densities; no noncompact Sobolev extension, full remainder gradient bound, or constrained Hartree evolution is claimed.'}
    tracked=subprocess.check_output(['git','ls-tree','-r','--name-only',BASE],text=True).splitlines()
    unchanged=[]
    for name in tracked:
        if not name.endswith('.lean'): continue
        old=subprocess.check_output(['git','show',BASE+':'+name])
        assert Path(name).read_bytes()==old, 'Existing Lean source changed: '+name
        unchanged.append(name)
    r['unchanged_existing_lean_sources']=len(unchanged)
    src=SOURCE.read_text()
    clean=mask_comments_and_strings(src)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',clean)
    names=['HBL.RegularRadiation.SpatialCore.'+n for n in re.findall(r'^(?:def|theorem)\s+(\w+)',clean,re.M)]
    assert len(names)>=7 and len(names)==len(set(names))
    r['audited_declarations']=names
    r['source_sha256']=hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    # No previously compiled object for the new target is accepted as evidence.
    removed=[]
    for folder in ['.lake/build/lib/lean/HBL','.lake/build/ir/HBL']:
        for p in Path(folder).glob(MODULE+'.*'):
            if p.is_file(): p.unlink(); removed.append(str(p))
    r['removed_new_target_cached_files']=removed
    r['build_exit']=command(['lake','build','HBL.'+MODULE],'spatial-build.log')
    if r['build_exit']==0:
        r['strict_exit']=command(['lake','env','lean','--trust=0','-DwarningAsError=true',str(SOURCE)],'spatial-strict.log')
        if r['strict_exit']==0:
            audit='import HBL.'+MODULE+'\nset_option pp.all true\nset_option pp.maxSteps 10000000\nset_option maxRecDepth 1000000\n'
            audit+='\n'.join('#check @'+n for n in names)+'\n'
            audit+='\n'.join('set_option pp.all false in\n#print axioms '+n for n in names)+'\n'
            p=Path('evidence/SpatialCoreAudit.lean'); p.write_text(audit)
            r['audit_exit']=command(['lake','env','lean','--trust=0','-DwarningAsError=true',str(p)],'spatial-complete-types.txt')
            text=Path('evidence/spatial-complete-types.txt').read_text()
            pat=r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
            found=[(m.group(1),m.group(2) or '') for m in re.finditer(pat,text,re.S)]
            allowed={'propext','Classical.choice','Quot.sound'}
            ok=(r['audit_exit']==0 and [n for n,_ in found]==names
                and all({x.strip() for x in a.split(',') if x.strip()}<=allowed for _,a in found)
                and not any(x in text for x in ['sorryAx','⋯','...']))
            r['audit_passed']=ok
            r['axioms']={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in found}
            if ok:
                r['retained_roots_build_exit']=command(['lake','build','HBL','HBL.SpectralBridgeTypes',*ROOTS],'retained-build.log')
                r['validation_passed']=r['retained_roots_build_exit']==0
    report_path=Path('verification/spatial-core-current-status.json')
    errors={name:diagnostic(name) for name in ['spatial-build.log','spatial-strict.log','spatial-complete-types.txt'] if (Path('evidence')/name).exists()}
    if r['retained_roots_build_exit'] not in [None,0]: errors['retained-build.log']=diagnostic('retained-build.log')
    report_path.write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
    Path('verification/spatial-core-current-errors.json').write_text(json.dumps(errors,ensure_ascii=False,indent=2)+'\n')
    Path('evidence/spatial-core-current-status.json').write_text(report_path.read_text())
    Path('evidence/HartreeSpatialCore.lean').write_text(src)
    print(json.dumps(r,ensure_ascii=False,indent=2))

if __name__=='__main__': main()
