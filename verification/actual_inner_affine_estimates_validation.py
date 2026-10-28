#!/usr/bin/env python3
"""Validate only the quantitative actual affine source estimates."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

PIN = "a98628e16c11f5167f16124105ddce53efa9bfe5"
MODULE = "HBL.ActualInnerAffineEstimates"
SOURCES = ["HBL/ActualInnerAffineEstimates.lean"]
AUDIT = "HBL/ActualInnerAffineEstimatesAudit.lean"
NAMES = ['HBL.Profile.ActualInner.actualPlusCharge_eq_twice_pairing', 'HBL.Profile.ActualInner.actualMinusCharge_eq_neg_pairing', 'HBL.Profile.ActualInner.actualPlusCharge_difference_le', 'HBL.Profile.ActualInner.actualMinusCharge_difference_le', 'HBL.Profile.ActualInner.weightedSourceDataL2_sub_const_mul', 'HBL.Profile.ActualInner.correctedPlusDataL2_eq', 'HBL.Profile.ActualInner.correctedMinusDataL2_eq', 'HBL.Profile.ActualInner.correctedPlusDataL2_difference_le', 'HBL.Profile.ActualInner.correctedMinusDataL2_difference_le']
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EVIDENCE = Path("verification/local-20261029/affine-estimates")
EVIDENCE.mkdir(parents=True, exist_ok=True)
report = {
    "validation_passed": False,
    "supporting_certificate_only": True,
    "target_original_environment": "prop:one-layer-stage3",
    "target_original_environment_closed": False,
    "strict_original_environment_count": "9/21",
    "main_PDE_theorem_closed": False,
}


def run(command, output_name, timeout=1200):
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=timeout)
    (EVIDENCE / output_name).write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"{command}: exit {result.returncode}; see {output_name}")
    return result.stdout


try:
    report["base_commit"] = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True).strip()
    compiler = run(["lean", "--version"], "compiler.txt", 60).strip()
    assert "4.35.0-rc3" in compiler, compiler
    report["compiler"] = compiler
    manifest = json.loads(Path("lake-manifest.json").read_text())
    revisions = {}
    for package in manifest["packages"]:
        revision = subprocess.check_output(
            ["git", "-C", ".lake/packages/" + package["name"], "rev-parse", "HEAD"],
            text=True).strip()
        assert revision == package["rev"], (package["name"], revision)
        revisions[package["name"]] = revision
    assert revisions["mathlib"] == PIN
    report["dependency_revisions"] = revisions

    from proofchain_scan import mask_comments_and_strings
    for filename in SOURCES + [AUDIT]:
        code = mask_comments_and_strings(Path(filename).read_text())
        assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code), filename
        assert not re.search(r"set_option\s+(?:linter\.|warningAsError\s+false)", code)
    audit_source = Path(AUDIT).read_text()
    assert re.findall(r"^#check @(\S+)", audit_source, re.M) == NAMES
    assert re.findall(r"^#print axioms (\S+)", audit_source, re.M) == NAMES

    run(["lake", "build", MODULE], "target-build.log")
    strict = {}
    for filename in SOURCES:
        run(["lake", "env", "lean", "--trust=0", "-DwarningAsError=true", filename],
            Path(filename).stem + "-strict.log")
        strict[filename] = 0
    report["strict_source_exit_codes"] = strict
    output = run(["lake", "env", "lean", "--trust=0", "-DwarningAsError=true", AUDIT],
                 "complete-types-and-axioms.txt")
    assert all(token not in output for token in ["sorryAx", "⋯", "…"])
    found = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
        output, re.S)
    assert [name for name, _ in found] == NAMES
    axioms = {}
    for name, raw in found:
        used = {item.strip() for item in raw.split(",") if item.strip()}
        assert used <= ALLOWED, (name, used)
        axioms[name] = sorted(used)
    report["axioms"] = axioms
    report["complete_type_output_bytes"] = len(output.encode())
    report["complete_type_output_sha256"] = hashlib.sha256(output.encode()).hexdigest()
    report["source_sha256"] = {
        filename: hashlib.sha256(Path(filename).read_bytes()).hexdigest()
        for filename in SOURCES + [AUDIT]
    }
    report["validation_passed"] = True
except Exception as error:
    report["error"] = repr(error)

Path("verification/actual-inner-affine-estimates-status.json").write_text(
    json.dumps(report, indent=2, ensure_ascii=False) + "\n")
print(json.dumps(report, indent=2, ensure_ascii=False))
raise SystemExit(0 if report["validation_passed"] else 1)
