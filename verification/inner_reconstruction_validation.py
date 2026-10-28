#!/usr/bin/env python3
"""Validate actual inner classical affine reconstruction, one theorem per file."""
from pathlib import Path
import hashlib
import gzip
import json
import re
import subprocess

PIN = "a98628e16c11f5167f16124105ddce53efa9bfe5"
MODULE = "HBL.InnerReconstruction.ActualClassicalAffineSolution"
SOURCES = ['HBL/InnerReconstruction/ActualClassicalAffineSolution.lean', 'HBL/InnerReconstruction/ActualTwoChannelReconstruction.lean', 'HBL/InnerReconstruction/AffineModelWeightedOutput.lean', 'HBL/InnerReconstruction/AffineRestorationDefinitions.lean', 'HBL/InnerReconstruction/AffineRestorationNonlocal.lean', 'HBL/InnerReconstruction/AffineRestorationPhaseEquation.lean', 'HBL/InnerReconstruction/AffineRestorationPlusEquation.lean', 'HBL/InnerReconstruction/AffineRestorationProperties.lean', 'HBL/InnerReconstruction/AffineRestorationSecondDerivative.lean', 'HBL/InnerReconstruction/BoundedWeightedOutput.lean', 'HBL/InnerReconstruction/CorrectedPhaseContinuous.lean', 'HBL/InnerReconstruction/CorrectedPlusContinuous.lean', 'HBL/InnerReconstruction/Definitions.lean', 'HBL/InnerReconstruction/FirstMoment.lean', 'HBL/InnerReconstruction/GreenBound.lean', 'HBL/InnerReconstruction/GreenKernelIntegrable.lean', 'HBL/InnerReconstruction/GreenLimit.lean', 'HBL/InnerReconstruction/GreenLipschitz.lean', 'HBL/InnerReconstruction/MomentWeight.lean', 'HBL/InnerReconstruction/OperatorRepresentative.lean', 'HBL/InnerReconstruction/PhaseClassicalEquation.lean', 'HBL/InnerReconstruction/PhaseRepresentative.lean', 'HBL/InnerReconstruction/PhaseSourceIdentification.lean', 'HBL/InnerReconstruction/PlusAffineSourceContinuous.lean', 'HBL/InnerReconstruction/PlusClassicalEquation.lean', 'HBL/InnerReconstruction/PlusRepresentative.lean', 'HBL/InnerReconstruction/PlusSourceIdentification.lean', 'HBL/InnerReconstruction/RepresentativeBound.lean', 'HBL/InnerReconstruction/RepresentativeContinuous.lean', 'HBL/InnerReconstruction/RepresentativeIntegralEquation.lean', 'HBL/InnerReconstruction/RepresentativeLimit.lean', 'HBL/InnerReconstruction/RepresentativeProperties.lean', 'HBL/InnerReconstruction/RepresentativeWeightedOutput.lean', 'HBL/InnerReconstruction/RepresentativeZero.lean', 'HBL/InnerReconstruction/SourceIntegrable.lean', 'HBL/InnerReconstruction/SourceOperatorRepresentative.lean']
AUDIT = "HBL/InnerReconstruction/ReconstructionAudit.lean"
NAMES = ['HBL.Modulation.Monopole.exists_actualInner_classical_affine', 'HBL.Modulation.Monopole.exists_actualInner_reconstructed', 'HBL.Modulation.Monopole.affineModel_inWeightedL2_neg', 'HBL.Modulation.Monopole.affineRestore_nonlocal', 'HBL.Modulation.Monopole.affineRestore_hMinus', 'HBL.Modulation.Monopole.affineRestore_hPlus', 'HBL.Modulation.Monopole.affineRestore_properties', 'HBL.Modulation.Monopole.affineRestore_second_hasDerivAt', 'HBL.Modulation.Monopole.bounded_continuous_inWeightedL2_neg', 'HBL.Modulation.Monopole.correctedMinusSource_continuous', 'HBL.Modulation.Monopole.correctedPlusSource_continuous', 'HBL.Modulation.Monopole.weightedSource_firstMoment_integrable', 'HBL.Modulation.Monopole.halfLineMinGreen_abs_le_firstMoment', 'HBL.Modulation.Monopole.halfLineMinGreen_kernel_integrable', 'HBL.Modulation.Monopole.halfLineMinGreen_tendsto_firstMoment', 'HBL.Modulation.Monopole.halfLineMinGreen_lipschitz', 'HBL.Modulation.Monopole.weightedSource_momentWeight_memLp', 'HBL.Modulation.Monopole.innerGreenRepresentative_ae_of_equation', 'HBL.Modulation.Monopole.phase_innerGreenRepresentative_classical', 'HBL.Modulation.Monopole.phase_innerGreenRepresentative_ae', 'HBL.Modulation.Monopole.phase_reconstructed_source_ae', 'HBL.Modulation.Monopole.hPlusAffineSource_continuous', 'HBL.Modulation.Monopole.plus_innerGreenRepresentative_classical', 'HBL.Modulation.Monopole.plus_innerGreenRepresentative_ae', 'HBL.Modulation.Monopole.plus_reconstructed_source_ae', 'HBL.Modulation.Monopole.innerGreenRepresentative_abs_le', 'HBL.Modulation.Monopole.innerGreenRepresentative_continuous', 'HBL.Modulation.Monopole.innerGreenRepresentative_eq_totalGreen', 'HBL.Modulation.Monopole.innerGreenRepresentative_tendsto', 'HBL.Modulation.Monopole.innerGreenRepresentative_properties', 'HBL.Modulation.Monopole.innerGreenRepresentative_inWeightedL2_neg', 'HBL.Modulation.Monopole.innerGreenRepresentative_zero', 'HBL.Modulation.Monopole.weightedSource_integrable', 'HBL.Modulation.Monopole.weightedSourceGreenOperator_ae_primitive']
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EVIDENCE = Path("verification/local-20261028/inner-reconstruction")
EVIDENCE.mkdir(parents=True, exist_ok=True)
report = {
    "validation_passed": False,
    "one_theorem_per_file": True,
    "new_supporting_theorems": 34,
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
    artifact = "verification/inner-reconstruction-types-and-axioms.txt.gz"
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

Path("verification/inner-reconstruction-status.json").write_text(
    json.dumps(report, indent=2, ensure_ascii=False) + "\n")
print(json.dumps(report, indent=2, ensure_ascii=False))
raise SystemExit(0 if report["validation_passed"] else 1)
