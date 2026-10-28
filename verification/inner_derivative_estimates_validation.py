#!/usr/bin/env python3
"""Validate actual first/second derivative bounds and affine slope limits, one theorem per file."""
from pathlib import Path
import hashlib
import gzip
import json
import re
import subprocess

PIN = "a98628e16c11f5167f16124105ddce53efa9bfe5"
MODULE = "HBL.InnerDerivatives.ActualDerivativeSolvers"
SOURCES = ['HBL/InnerDerivatives/ActualDerivativeSolvers.lean', 'HBL/InnerDerivatives/AffineDerivativeFar.lean', 'HBL/InnerDerivatives/AffineDerivativeLimit.lean', 'HBL/InnerDerivatives/AffineSecondWeighted.lean', 'HBL/InnerDerivatives/Definitions.lean', 'HBL/InnerDerivatives/GreenDerivativeBound.lean', 'HBL/InnerDerivatives/GreenDerivativeDifference.lean', 'HBL/InnerDerivatives/MinusDerivativeBound.lean', 'HBL/InnerDerivatives/MinusDerivativeDifference.lean', 'HBL/InnerDerivatives/MinusDerivativeIdentity.lean', 'HBL/InnerDerivatives/MinusDerivativeWeighted.lean', 'HBL/InnerDerivatives/MinusDerivativeWeightedDifference.lean', 'HBL/InnerDerivatives/MinusOutputDerivativeTail.lean', 'HBL/InnerDerivatives/MinusOutputSecondBound.lean', 'HBL/InnerDerivatives/MinusSecondBound.lean', 'HBL/InnerDerivatives/MinusSecondDifference.lean', 'HBL/InnerDerivatives/MinusSecondIdentity.lean', 'HBL/InnerDerivatives/PlusDerivativeBound.lean', 'HBL/InnerDerivatives/PlusDerivativeDifference.lean', 'HBL/InnerDerivatives/PlusDerivativeIdentity.lean', 'HBL/InnerDerivatives/PlusDerivativeWeighted.lean', 'HBL/InnerDerivatives/PlusDerivativeWeightedDifference.lean', 'HBL/InnerDerivatives/PlusOutputDerivativeTail.lean', 'HBL/InnerDerivatives/PlusOutputSecondBound.lean', 'HBL/InnerDerivatives/PlusSecondBound.lean', 'HBL/InnerDerivatives/PlusSecondDifference.lean', 'HBL/InnerDerivatives/PlusSecondIdentity.lean', 'HBL/InnerDerivatives/RemainderZero.lean', 'HBL/InnerDerivatives/SecondDefinitions.lean', 'HBL/InnerDerivatives/SecondSourceBound.lean', 'HBL/InnerDerivatives/SecondSourceDifference.lean', 'HBL/InnerDerivatives/SourceNorm.lean', 'HBL/InnerDerivatives/TailMomentBound.lean', 'HBL/InnerDerivatives/TotalSourceNorm.lean', 'HBL/InnerDerivatives/WeightedAETransfer.lean', 'HBL/InnerDerivatives/WeightedDecayBound.lean', 'HBL/InnerDerivatives/WeightedPotentialNorm.lean']
AUDIT = "HBL/InnerDerivatives/DerivativesAudit.lean"
NAMES = ['HBL.Modulation.Monopole.exists_actualInner_derivative_estimates', 'HBL.Modulation.Monopole.affineRestore_deriv_far', 'HBL.Modulation.Monopole.affineRestore_derivative_limit', 'HBL.Modulation.Monopole.affineRestore_second_weighted_bound', 'HBL.Modulation.Monopole.innerGreenDerivative_bound', 'HBL.Modulation.Monopole.innerGreenDerivative_difference_le', 'HBL.Modulation.Monopole.normalizedMinusRemainder_derivative_bound', 'HBL.Modulation.Monopole.normalizedMinusRemainder_derivative_difference_le', 'HBL.Modulation.Monopole.normalizedMinusRemainder_hasDerivAt', 'HBL.Modulation.Monopole.normalizedMinusRemainder_derivative_weighted', 'HBL.Modulation.Monopole.normalizedMinusRemainder_derivative_weighted_difference', 'HBL.Modulation.Monopole.normalizedMinusOutput_derivative_tail', 'HBL.Modulation.Monopole.normalizedMinusOutput_second_derivative_bound', 'HBL.Modulation.Monopole.normalizedMinusRemainder_second_derivative_bound', 'HBL.Modulation.Monopole.normalizedMinusRemainder_second_derivative_difference', 'HBL.Modulation.Monopole.normalizedMinusRemainder_second_derivative_ae', 'HBL.Modulation.Monopole.normalizedPlusRemainder_derivative_bound', 'HBL.Modulation.Monopole.normalizedPlusRemainder_derivative_difference_le', 'HBL.Modulation.Monopole.normalizedPlusRemainder_hasDerivAt', 'HBL.Modulation.Monopole.normalizedPlusRemainder_derivative_weighted', 'HBL.Modulation.Monopole.normalizedPlusRemainder_derivative_weighted_difference', 'HBL.Modulation.Monopole.normalizedPlusOutput_derivative_tail', 'HBL.Modulation.Monopole.normalizedPlusOutput_second_derivative_bound', 'HBL.Modulation.Monopole.normalizedPlusRemainder_second_derivative_bound', 'HBL.Modulation.Monopole.normalizedPlusRemainder_second_derivative_difference', 'HBL.Modulation.Monopole.normalizedPlusRemainder_second_derivative_ae', 'HBL.Modulation.Monopole.normalizedRemainder_zero', 'HBL.Modulation.Monopole.inner_second_source_bound', 'HBL.Modulation.Monopole.inner_second_source_difference_le', 'HBL.Modulation.Monopole.inner_source_integral_norm_le', 'HBL.Modulation.Monopole.halfLineGreenTail_moment_bound', 'HBL.Modulation.Monopole.inner_totalSource_integral_norm_le', 'HBL.Modulation.Monopole.innerWeighted_ae_transfer', 'HBL.Modulation.Monopole.innerWeightedNorm_le_of_inverse_linear_bound', 'HBL.Modulation.Monopole.inner_weighted_potential_norm_le']
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EVIDENCE = Path("verification/local-20261029/inner-derivative-estimates")
EVIDENCE.mkdir(parents=True, exist_ok=True)
report = {
    "validation_passed": False,
    "one_theorem_per_file": True,
    "new_supporting_theorems": 35,
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
    assert "4.35.0-rc3" in compiler and "470d5ce1400764999581fd26d5d72b00d990b0f4" in compiler, compiler
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
        assert len(re.findall(r"^(?:theorem|lemma) ", code, re.M)) <= 1, filename
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
        used = {re.sub(r"\.\{[^}]*\}$", "", item.strip()) for item in raw.split(",") if item.strip()}
        assert used <= ALLOWED, (name, used)
        axioms[name] = sorted(used)
    report["axioms"] = axioms
    compressed = gzip.compress(output.encode(), mtime=0)
    assert gzip.decompress(compressed) == output.encode()
    artifact = "verification/inner-derivative-estimates-types-and-axioms.txt.gz"
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

Path("verification/inner-derivative-estimates-status.json").write_text(
    json.dumps(report, indent=2, ensure_ascii=False) + "\n")
print(json.dumps(report, indent=2, ensure_ascii=False))
raise SystemExit(0 if report["validation_passed"] else 1)
