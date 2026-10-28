#!/usr/bin/env python3
"""Validate actual weighted inner inverse bounds and stability, one theorem per file."""
from pathlib import Path
import hashlib
import gzip
import json
import re
import subprocess

PIN = "a98628e16c11f5167f16124105ddce53efa9bfe5"
MODULE = "HBL.InnerEstimates.ActualBoundedSolvers"
SOURCES = ['HBL/InnerEstimates/ActualBoundedSolvers.lean', 'HBL/InnerEstimates/AffineWeightedDifference.lean', 'HBL/InnerEstimates/BoundedWeightedNorm.lean', 'HBL/InnerEstimates/Definitions.lean', 'HBL/InnerEstimates/FirstMomentNorm.lean', 'HBL/InnerEstimates/FredholmDifference.lean', 'HBL/InnerEstimates/GreenBoundNorm.lean', 'HBL/InnerEstimates/GreenPrimitiveNorm.lean', 'HBL/InnerEstimates/IntegralCauchySchwarz.lean', 'HBL/InnerEstimates/MinusEquation.lean', 'HBL/InnerEstimates/MinusHilbertDifference.lean', 'HBL/InnerEstimates/MinusOutputBound.lean', 'HBL/InnerEstimates/MinusOutputClassical.lean', 'HBL/InnerEstimates/MinusOutputDifference.lean', 'HBL/InnerEstimates/MinusOutputProperties.lean', 'HBL/InnerEstimates/MinusRemainderDifference.lean', 'HBL/InnerEstimates/MinusRemainderProperties.lean', 'HBL/InnerEstimates/MinusRemainderWeightedDifference.lean', 'HBL/InnerEstimates/NormalizedZero.lean', 'HBL/InnerEstimates/OutputZero.lean', 'HBL/InnerEstimates/PlusEquation.lean', 'HBL/InnerEstimates/PlusHilbertDifference.lean', 'HBL/InnerEstimates/PlusOutputBound.lean', 'HBL/InnerEstimates/PlusOutputClassical.lean', 'HBL/InnerEstimates/PlusOutputDifference.lean', 'HBL/InnerEstimates/PlusOutputProperties.lean', 'HBL/InnerEstimates/PlusRemainderDifference.lean', 'HBL/InnerEstimates/PlusRemainderProperties.lean', 'HBL/InnerEstimates/PlusRemainderWeightedDifference.lean', 'HBL/InnerEstimates/RepresentativeDifferenceBound.lean', 'HBL/InnerEstimates/RepresentativeDifferenceIdentity.lean', 'HBL/InnerEstimates/RepresentativeZeroSource.lean', 'HBL/InnerEstimates/WeightedAffineNorm.lean', 'HBL/InnerEstimates/WeightedNormDifference.lean', 'HBL/InnerEstimates/WeightedNormIdentity.lean', 'HBL/InnerEstimates/WeightedNormNonnegative.lean', 'HBL/InnerEstimates/WeightedSubMembership.lean', 'HBL/InnerEstimates/ZeroData.lean']
AUDIT = "HBL/InnerEstimates/EstimatesAudit.lean"
NAMES = ['HBL.Modulation.Monopole.exists_actualInner_bounded_classical_solvers', 'HBL.Modulation.Monopole.affineRestore_weighted_difference_bound', 'HBL.Modulation.Monopole.innerWeightedNorm_le_of_bound', 'HBL.Modulation.Monopole.inner_firstMoment_norm_le', 'HBL.Modulation.Monopole.innerFredholm_norm_sub_le', 'HBL.Modulation.Monopole.innerGreenBound_norm_le', 'HBL.Modulation.Monopole.inner_greenPrimitiveBound_le', 'HBL.Modulation.Monopole.inner_integral_norm_mul_le', 'HBL.Modulation.Monopole.normalizedMinusInner_equation', 'HBL.Modulation.Monopole.normalizedMinusInner_difference_le', 'HBL.Modulation.Monopole.normalizedMinusOutput_weighted_norm_le', 'HBL.Modulation.Monopole.normalizedMinusOutput_classical', 'HBL.Modulation.Monopole.normalizedMinusOutput_weighted_difference_le', 'HBL.Modulation.Monopole.normalizedMinusOutput_properties', 'HBL.Modulation.Monopole.normalizedMinusRemainder_difference_le', 'HBL.Modulation.Monopole.normalizedMinusRemainder_properties', 'HBL.Modulation.Monopole.normalizedMinusRemainder_weighted_difference_le', 'HBL.Modulation.Monopole.normalizedInner_zero', 'HBL.Modulation.Monopole.normalizedOutput_zero', 'HBL.Modulation.Monopole.normalizedPlusInner_equation', 'HBL.Modulation.Monopole.normalizedPlusInner_difference_le', 'HBL.Modulation.Monopole.normalizedPlusOutput_weighted_norm_le', 'HBL.Modulation.Monopole.normalizedPlusOutput_classical', 'HBL.Modulation.Monopole.normalizedPlusOutput_weighted_difference_le', 'HBL.Modulation.Monopole.normalizedPlusOutput_properties', 'HBL.Modulation.Monopole.normalizedPlusRemainder_difference_le', 'HBL.Modulation.Monopole.normalizedPlusRemainder_properties', 'HBL.Modulation.Monopole.normalizedPlusRemainder_weighted_difference_le', 'HBL.Modulation.Monopole.innerGreenRepresentative_difference_le', 'HBL.Modulation.Monopole.innerGreenRepresentative_sub', 'HBL.Modulation.Monopole.innerGreenRepresentative_zero_source', 'HBL.Modulation.Monopole.innerWeighted_sub_const_mul_bound', 'HBL.Modulation.Monopole.innerWeightedNorm_sub_eq', 'HBL.Modulation.Monopole.innerWeightedNorm_eq', 'HBL.Modulation.Monopole.innerWeightedNorm_nonneg', 'HBL.Modulation.Monopole.innerWeighted_sub_mem', 'HBL.Modulation.Monopole.innerWeightedData_zero']
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EVIDENCE = Path("verification/local-20261029/inner-weighted-estimates")
EVIDENCE.mkdir(parents=True, exist_ok=True)
report = {
    "validation_passed": False,
    "one_theorem_per_file": True,
    "new_supporting_theorems": 37,
    "supporting_certificate_only": True,
    "target_original_environment": "prop:one-layer-stage3",
    "target_original_environment_closed": False,
    "strict_original_environment_count": "9/21",
    "main_PDE_theorem_closed": False,
}


def run(command, output_name, timeout=1200):
    print("Checking " + output_name, flush=True)
    with (EVIDENCE / output_name).open("w") as log:
        result = subprocess.run(command, text=True, stdout=log,
                                stderr=subprocess.STDOUT, timeout=timeout)
    output = (EVIDENCE / output_name).read_text()
    if result.returncode:
        raise RuntimeError(f"{command}: exit {result.returncode}; see {output_name}")
    return output


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
        assert len(re.findall(r"^theorem ", code, re.M)) <= 1, filename
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
    compressed = gzip.compress(output.encode(), mtime=0)
    assert gzip.decompress(compressed) == output.encode()
    artifact = "verification/inner-weighted-estimates-types-and-axioms.txt.gz"
    Path(artifact).write_bytes(compressed)
    report["complete_type_output_artifact"] = artifact
    report["compressed_output_bytes"] = len(compressed)
    report["compressed_output_sha256"] = hashlib.sha256(compressed).hexdigest()
    report["complete_type_output_bytes"] = len(output.encode())
    report["complete_type_output_sha256"] = hashlib.sha256(output.encode()).hexdigest()
    report["source_sha256"] = {
        filename: hashlib.sha256(Path(filename).read_bytes()).hexdigest()
        for filename in SOURCES + [AUDIT]
    }
    report["validation_passed"] = True
except Exception as error:
    report["error"] = repr(error)

Path("verification/inner-weighted-estimates-status.json").write_text(
    json.dumps(report, indent=2, ensure_ascii=False) + "\n")
print(json.dumps(report, indent=2, ensure_ascii=False))
raise SystemExit(0 if report["validation_passed"] else 1)
