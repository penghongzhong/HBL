#!/usr/bin/env python3
"""Validate the unique compact-parameter Kummer boundary problem, one theorem per file."""
from pathlib import Path
import hashlib
import gzip
import json
import re
import subprocess
import os
import tempfile
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

PIN = "a98628e16c11f5167f16124105ddce53efa9bfe5"
MODULE = 'HBL.KummerBoundaryUnique.ActualCompactUniqueFamily'
SOURCES = ['HBL/KummerBoundaryUnique/ActualCompactUniqueFamily.lean', 'HBL/KummerBoundaryUnique/BaseUniqueness.lean', 'HBL/KummerBoundaryUnique/BoundedUniqueFamily.lean', 'HBL/KummerBoundaryUnique/CertificateSolution.lean', 'HBL/KummerBoundaryUnique/CoefficientShift.lean', 'HBL/KummerBoundaryUnique/Definitions.lean', 'HBL/KummerBoundaryUnique/HomogeneousCoordinates.lean', 'HBL/KummerBoundaryUnique/HomogeneousZero.lean', 'HBL/KummerBoundaryUnique/PerturbedUniqueness.lean', 'HBL/KummerBoundaryUnique/ResidualBound.lean', 'HBL/KummerBoundaryUnique/SolutionDifference.lean']
FOUNDATION_SOURCES = ['HBL/KummerCompactFamily/CompactJetBound.lean', 'HBL/KummerCompactFamily/CompactParameterBound.lean', 'HBL/KummerCompactFamily/ComplexAnalytic.lean', 'HBL/KummerCompactFamily/PhysicalAnalytic.lean', 'HBL/KummerCompactFamily/RadiusChoice.lean', 'HBL/KummerCompactFamily/SmallBaseInverse.lean', 'HBL/KummerLocalInverse/ActualPair.lean', 'HBL/KummerLocalInverse/ActualRightInverse.lean', 'HBL/KummerLocalInverse/C1Bound.lean', 'HBL/KummerLocalInverse/CertificateDefinitions.lean', 'HBL/KummerLocalInverse/CoefficientBounds.lean', 'HBL/KummerLocalInverse/CoefficientDerivatives.lean', 'HBL/KummerLocalInverse/Definitions.lean', 'HBL/KummerLocalInverse/EndpointNormalization.lean', 'HBL/KummerLocalInverse/Equation.lean', 'HBL/KummerLocalInverse/JetBound.lean', 'HBL/KummerLocalInverse/JetDefinitions.lean', 'HBL/KummerLocalInverse/JetLinearity.lean', 'HBL/KummerLocalInverse/OperatorBound.lean', 'HBL/KummerLocalInverse/OperatorCertificate.lean', 'HBL/KummerLocalInverse/OperatorDefinitions.lean', 'HBL/KummerLocalInverse/OperatorStability.lean', 'HBL/KummerLocalInverse/PhysicalBounds.lean', 'HBL/KummerLocalInverse/PhysicalClassical.lean', 'HBL/KummerLocalInverse/PhysicalDefinitions.lean', 'HBL/KummerLocalInverse/PhysicalDerivatives.lean', 'HBL/KummerLocalInverse/PhysicalEndpoints.lean', 'HBL/KummerLocalInverse/PhysicalEquation.lean', 'HBL/KummerLocalInverse/PhysicalLinearity.lean', 'HBL/KummerLocalInverse/SecondDerivative.lean', 'HBL/KummerLocalInverse/SourceBounds.lean', 'HBL/KummerLocalInverse/SourceExtension.lean', 'HBL/KummerLocalInverse/SourceExtensionDefinitions.lean', 'HBL/KummerLocalInverse/SourceLinearity.lean', 'HBL/KummerLocalInverse/SourceRegularity.lean', 'HBL/KummerLocalInverse/ValueDerivative.lean', 'HBL/KummerLocalInverse/ValueLinearity.lean', 'HBL/KummerParameterInverse/BlockUnit.lean', 'HBL/KummerParameterInverse/ClassicalCertificate.lean', 'HBL/KummerParameterInverse/CoefficientDifference.lean', 'HBL/KummerParameterInverse/Definitions.lean', 'HBL/KummerParameterInverse/OperatorBound.lean', 'HBL/KummerParameterInverse/OperatorDerivative.lean', 'HBL/KummerParameterInverse/OperatorDifference.lean', 'HBL/KummerParameterInverse/OperatorLipschitz.lean', 'HBL/KummerParameterInverse/PhysicalParameterDerivatives.lean', 'HBL/KummerParameterInverse/ResolventBound.lean', 'HBL/KummerParameterInverse/ResolventDerivative.lean', 'HBL/KummerParameterInverse/ResolventDifference.lean', 'HBL/KummerParameterInverse/ResolventIdentities.lean', 'HBL/KummerParameterInverse/SourceStability.lean', 'HBL/KummerParameterInverse/ValueBound.lean']
BUILD_SOURCES = SOURCES + FOUNDATION_SOURCES
AUDIT = 'HBL/KummerBoundaryUnique/BoundaryUniqueAudit.lean'
NAMES = ['HBL.Profile.Kummer.exists_actual_compact_parameter_kummer_unique_family', 'HBL.Profile.Kummer.kummer_base_boundary_solution_unique', 'HBL.Profile.Kummer.exists_actual_bounded_parameter_kummer_unique_family', 'HBL.Profile.Kummer.kummer_inverse_boundary_solution', 'HBL.Profile.Kummer.kummer_boundary_solution_shift', 'HBL.Profile.Kummer.kummer_homogeneous_coordinates_derivative', 'HBL.Profile.Kummer.kummer_homogeneous_boundary_zero', 'HBL.Profile.Kummer.annulusParameterInverse_boundary_iff', 'HBL.Profile.Kummer.kummer_boundary_residual_bound', 'HBL.Profile.Kummer.kummer_boundary_solution_sub']
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EVIDENCE = Path("verification/local-20261029/kummer-boundary-unique")
EVIDENCE.mkdir(parents=True, exist_ok=True)
report = {
    "validation_passed": False,
    "one_theorem_per_file": True,
    "new_supporting_theorems": 10,
    "supporting_certificate_only": True,
    "target_original_environment": "prop:one-layer-stage3",
    "target_original_environment_closed": False,
    "strict_original_environment_count": "9/21",
    "main_PDE_theorem_closed": False,
}


def run(command, output_name, timeout=1200, env=None):
    print("Checking " + output_name, flush=True)
    with (EVIDENCE / output_name).open("w") as log:
        result = subprocess.run(command, text=True, stdout=log,
                                stderr=subprocess.STDOUT, timeout=timeout, env=env)
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

    source_snapshot = {filename: hashlib.sha256(Path(filename).read_bytes()).hexdigest() for filename in BUILD_SOURCES + [AUDIT]}
    from proofchain_scan import mask_comments_and_strings
    for filename in BUILD_SOURCES + [AUDIT]:
        code = mask_comments_and_strings(Path(filename).read_text())
        assert len(re.findall(r"^(?:theorem|lemma) ", code, re.M)) <= 1, filename
        assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code), filename
        assert not re.search(r"set_option\s+(?:linter\.|warningAsError\s+false)", code)
    audit_source = Path(AUDIT).read_text()
    assert re.findall(r"^#check @(\S+)", audit_source, re.M) == NAMES
    assert re.findall(r"^#print axioms (\S+)", audit_source, re.M) == NAMES

    reached = set()
    def visit_source(filename):
        if filename in reached:
            return
        reached.add(filename)
        for module in re.findall(r"^import (HBL\.(?:Kummer(?:Local|Parameter)Inverse|KummerCompactFamily|KummerBoundaryUnique)\.\w+)", Path(filename).read_text(), re.M):
            visit_source(module.replace(".", "/") + ".lean")
    visit_source(MODULE.replace(".", "/") + ".lean")
    assert reached == set(BUILD_SOURCES), (reached ^ set(BUILD_SOURCES))
    run(["lake", "build", "HBL.KummerLocalInverse.ActualRightInverse"], "foundation-build.log")
    # Keep fresh artifacts outside the synchronized workspace: old .olean files
    # can otherwise be restored while a source-level check is running.
    isolated = Path(tempfile.mkdtemp(prefix="hbl-kummer-unique-strict-"))
    # Lean selects a search root by top-level module directory, so expose the
    # unchanged historical HBL dependencies in the same root as the new block.
    (isolated / "HBL").mkdir()
    for entry in Path(".lake/build/lib/lean/HBL").iterdir():
        if entry.name not in {"KummerLocalInverse", "KummerParameterInverse", "KummerCompactFamily", "KummerBoundaryUnique"}:
            (isolated / "HBL" / entry.name).symlink_to(entry.resolve(), target_is_directory=entry.is_dir())
    env = os.environ.copy()
    inherited_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], text=True).strip()
    env["LEAN_PATH"] = str(isolated) + os.pathsep + inherited_path
    imports = {
        filename: {m.replace(".", "/") + ".lean" for m in re.findall(
            r"^import (HBL\.(?:Kummer(?:Local|Parameter)Inverse|KummerCompactFamily|KummerBoundaryUnique)\.\w+)", Path(filename).read_text(), re.M)}
        for filename in BUILD_SOURCES
    }
    strict = {}
    pending = set(BUILD_SOURCES)
    def compile_source(filename):
        target = isolated / Path(filename).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        run(["lean", "--trust=0", "-DwarningAsError=true", "-o", str(target), filename],
            filename.replace("/", "_") + "-strict.log", env=env)
        return filename
    with ThreadPoolExecutor(max_workers=3) as pool:
        running = {}
        while pending or running:
            ready = sorted(f for f in pending if imports[f] <= strict.keys())
            for filename in ready[:3 - len(running)]:
                pending.remove(filename)
                running[pool.submit(compile_source, filename)] = filename
            assert running, "Cyclic local import graph"
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                strict[future.result()] = 0
                del running[future]
    report["strict_source_exit_codes"] = {f: strict[f] for f in SOURCES}
    report["foundation_strict_exit_codes"] = {f: strict[f] for f in FOUNDATION_SOURCES}
    artifacts = {f: isolated / Path(f).with_suffix(".olean") for f in BUILD_SOURCES}
    artifact_snapshot = {f: hashlib.sha256(p.read_bytes()).hexdigest() for f, p in artifacts.items()}
    output = run(["lean", "--trust=0", "-DwarningAsError=true", AUDIT],
                 "complete-types-and-axioms.txt", env=env)
    assert artifact_snapshot == {f: hashlib.sha256(p.read_bytes()).hexdigest() for f, p in artifacts.items()}
    report["isolated_fresh_compilation"] = True
    report["compiled_source_sha256"] = artifact_snapshot
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
    artifact = "verification/kummer-boundary-unique-types-and-axioms.txt.gz"
    Path(artifact).write_bytes(compressed)
    report["complete_type_output_artifact"] = artifact
    report["compressed_output_bytes"] = len(compressed)
    report["compressed_output_sha256"] = hashlib.sha256(compressed).hexdigest()
    report["complete_type_output_bytes"] = len(output.encode())
    report["complete_type_output_sha256"] = hashlib.sha256(output.encode()).hexdigest()
    report["source_sha256"] = {
        filename: hashlib.sha256(Path(filename).read_bytes()).hexdigest()
        for filename in BUILD_SOURCES + [AUDIT]
    }
    assert report["source_sha256"] == source_snapshot, "Sources changed during validation"
    report["all_new_sources_on_terminal_import_chain"] = True
    report["scope"] = "For any compact real (mu, theta) parameter set and fixed z>0, a single constructed positive annulus carries a classical family which is the unique solution of the fixed separated endpoint problem. Arbitrary classical boundary jets satisfy a source-residual error bound, with constants uniform on the parameter set. Analyticity, both physical parameter derivatives and all finite parameter-jet bounds are retained. A prescribed matching annulus and manuscript weighted/nonlinear residual estimates remain open."
    report["validation_passed"] = True
except Exception as error:
    report["error"] = repr(error)

Path("verification/kummer-boundary-unique-status.json").write_text(
    json.dumps(report, indent=2, ensure_ascii=False) + "\n")
print(json.dumps(report, indent=2, ensure_ascii=False))
raise SystemExit(0 if report["validation_passed"] else 1)
