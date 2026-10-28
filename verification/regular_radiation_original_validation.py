#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, subprocess, sys

TARGET = "HBL/RegularRadiationOriginalEnvironment.lean"
MODULE = "HBL.RegularRadiationOriginalEnvironment"
NAMES = [
  "HBL.RegularRadiation.UnitTime",
  "HBL.RegularRadiation.RegularRadiationPath",
  "HBL.RegularRadiation.terminalAffineTime",
  "HBL.RegularRadiation.IsRegularHartreeSolutionOn",
  "HBL.RegularRadiation.CitedHighRegularityHartreeLocalTheory",
  "HBL.RegularRadiation.cited_flow_is_regular_solution",
  "HBL.RegularRadiation.regularRadiationFlow_originalEnvironment_closed",
]
ALLOWED = {"propext","Classical.choice","Quot.sound"}
STATUS = Path("verification/regular-radiation-original-current-status.json")
ERRORS = Path("verification/regular-radiation-original-current-errors.json")
EVID = Path("evidence/regular-radiation-original")
EVID.mkdir(parents=True, exist_ok=True)

def run(cmd, name, timeout=1200):
    try:
        p=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
        code,out=p.returncode,p.stdout
    except subprocess.TimeoutExpired as exc:
        code=124; out=exc.stdout or ""
        if isinstance(out,bytes): out=out.decode(errors="replace")
        out += "\nVALIDATOR timeout\n"
    (EVID/name).write_text(out)
    return code,out

report = {
  "source_commit": os.environ.get("GITHUB_SHA","local"),
  "run_id": os.environ.get("GITHUB_RUN_ID","local"),
  "validation_passed": False,
  "original_environment": "prop:regular-flow-stage3",
  "terminal": "HBL.RegularRadiation.regularRadiationFlow_originalEnvironment_closed",
  "external_literature_interface_explicit": True,
  "standard_local_theory_reproved_in_lean": False,
  "new_lean_axiom": False,
  "original_environment_specialization_complete": False,
  "main_theorem_closed": False,
  "full_paper_21_of_21_certified": False,
}
errors = {}

try:
    c,v=run(["lean","--version"],"compiler.txt",60)
    assert c==0 and "4.35.0-rc3" in v,v
    mh=subprocess.check_output(["git","-C",".lake/packages/mathlib","rev-parse","HEAD"],text=True).strip()
    assert mh=="a98628e16c11f5167f16124105ddce53efa9bfe5",mh
    report["compiler"]=v.strip()
    report["mathlib_commit"]=mh

    sys.path.insert(0,"verification")
    from proofchain_scan import mask_comments_and_strings, ROOTS
    code=mask_comments_and_strings(Path(TARGET).read_text())
    assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b",code)
    assert not re.search(r"set_option\s+(?:linter\.|warningAsError\s+false)",code)

    b,_=run(["lake","build",MODULE],"build.log",1200)
    report["build_exit"]=b
    assert b==0,"target build failed"

    s,_=run(["lake","env","lean","--trust=0","-DwarningAsError=true",TARGET],"strict.log",1200)
    report["strict_exit"]=s
    assert s==0,"strict compilation failed"

    audit = "import "+MODULE+"\nset_option pp.all true\nset_option pp.maxSteps 20000000\nset_option maxRecDepth 1000000\n"
    audit += "\n".join("#check @"+n for n in NAMES)+"\n"
    audit += "\n".join("set_option pp.all false in\n#print axioms "+n for n in NAMES)+"\n"
    ap=EVID/"RegularRadiationOriginalAudit.lean"
    ap.write_text(audit)
    ae,out=run(["lake","env","lean","--trust=0","-DwarningAsError=true",str(ap)],
               "complete-types-and-axioms.txt",1200)
    report["audit_exit"]=ae
    assert ae==0,"complete type / axiom audit failed"
    assert "sorryAx" not in out and "⋯" not in out and "…" not in out
    found=[(m.group(1),m.group(2) or "") for m in re.finditer(
      r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",out,re.S)]
    assert [n for n,_ in found]==NAMES,([n for n,_ in found],NAMES)
    ax={}
    for n,raw in found:
        aset={a.strip() for a in raw.split(",") if a.strip()}
        assert aset<=ALLOWED,(n,aset)
        ax[n]=sorted(aset)
    report["axioms"]=ax
    report["complete_type_output_bytes"]=len(out.encode())
    report["complete_type_output_sha256"]=hashlib.sha256(out.encode()).hexdigest()
    report["source_sha256"]=hashlib.sha256(Path(TARGET).read_bytes()).hexdigest()

    # Regression only on the already retained main roots, not on every historical file.
    rb,_=run(["lake","build",*ROOTS],"retained-roots.log",1200)
    report["retained_component_roots"]=len(ROOTS)
    report["retained_roots_build_exit"]=rb
    assert rb==0,"retained-root regression failed"

    report["original_environment_specialization_complete"]=True
    report["validation_passed"]=True
except Exception as exc:
    errors["exception"]=repr(exc)

STATUS.write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n")
ERRORS.write_text(json.dumps(errors,ensure_ascii=False,indent=2)+"\n")
(EVID/"status.json").write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n")
(EVID/"errors.json").write_text(json.dumps(errors,ensure_ascii=False,indent=2)+"\n")
print(json.dumps(report,ensure_ascii=False,indent=2))
print(json.dumps(errors,ensure_ascii=False,indent=2))
raise SystemExit(0 if report["validation_passed"] else 1)
