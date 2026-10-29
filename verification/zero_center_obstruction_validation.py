#!/usr/bin/env python3
"""Fresh kernel check of the finite-dimensional zero-centre obstruction.

This diagnostic does not close any original manuscript environment.
Run from the repository root with the pinned Lean toolchain on PATH.
"""
from pathlib import Path
import gzip
import hashlib
import json
import os
import re
import subprocess
import tempfile

from proofchain_scan import mask_comments_and_strings

PREFIX = "HBL.ZeroCenterObstruction."
SOURCES = [
    "HBL/ZeroCenterObstruction/Definitions.lean",
    "HBL/ZeroCenterObstruction/StaticDataCounterexample.lean",
]
AUDIT = "HBL/ZeroCenterObstruction/ObstructionAudit.lean"
NAME = PREFIX + "static_data_do_not_force_zero_center_splitting"
DEFINITIONS = [PREFIX + n for n in [
    "Plane", "State", "dot", "symplecticLinear", "hessianLinear", "J", "L", "A",
    "zeroMode", "centerMode", "plusMode", "minusMode", "graphMode",
    "HasInvariantZeroProjection",
]]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EVIDENCE = Path(tempfile.mkdtemp(prefix="hbl-zero-centre-strict-"))
report = {
    "validation_passed": False,
    "diagnostic_counterexample_only": True,
    "new_supporting_theorems": 1,
    "newly_accepted_original_environments": 0,
    "strict_original_environment_count": "9/21",
    "main_PDE_theorem_closed": False,
    "not_a_counterexample_to_the_Hartree_PDE": True,
}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(command, name, env=None):
    print("Checking " + name, flush=True)
    log = EVIDENCE / name
    with log.open("w") as out:
        result = subprocess.run(command, text=True, stdout=out,
                                stderr=subprocess.STDOUT, timeout=600, env=env)
    if result.returncode:
        raise RuntimeError(f"exit {result.returncode}: see {log}")
    return log.read_text()


try:
    report["base_commit"] = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True).strip()
    compiler = run(["lean", "--version"], "compiler.txt").strip()
    assert "4.35.0-rc3" in compiler
    assert "470d5ce1400764999581fd26d5d72b00d990b0f4" in compiler
    report["compiler"] = compiler
    revisions = {}
    for package in json.loads(Path("lake-manifest.json").read_text())["packages"]:
        revision = subprocess.check_output(
            ["git", "-C", ".lake/packages/" + package["name"], "rev-parse", "HEAD"],
            text=True).strip()
        assert revision == package["rev"], (package["name"], revision)
        revisions[package["name"]] = revision
    assert revisions["mathlib"] == "a98628e16c11f5167f16124105ddce53efa9bfe5"
    report["dependency_revisions"] = revisions

    snapshot = {f: digest(f) for f in SOURCES + [AUDIT]}
    for filename in SOURCES + [AUDIT]:
        code = mask_comments_and_strings(Path(filename).read_text())
        count = len(re.findall(r"^(?:theorem|lemma) ", code, re.M))
        assert count == int(filename == SOURCES[1]), (filename, count)
        assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code)
        assert not re.search(r"set_option\s+(?:linter\.|warningAsError\s+false)", code)
    report["one_theorem_per_file"] = True
    audit = Path(AUDIT).read_text()
    assert re.findall(r"^#check @(\S+)", audit, re.M) == [NAME]
    assert re.findall(r"^#print axioms (\S+)", audit, re.M) == [NAME]
    assert all("#print " + name + "\n" in audit for name in DEFINITIONS)
    # The only local dependencies are these two fresh source modules.
    reached = set()
    def visit(filename):
        if filename in reached:
            return
        reached.add(filename)
        for module in re.findall(r"^import (HBL\.\S+)", Path(filename).read_text(), re.M):
            visit(module.replace(".", "/") + ".lean")
    visit(SOURCES[1])
    assert reached == set(SOURCES), reached

    isolated = EVIDENCE / "lib"
    env = os.environ.copy()
    inherited = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], text=True).strip()
    env["LEAN_PATH"] = str(isolated) + os.pathsep + inherited
    artifacts = {}
    for filename in SOURCES:
        target = isolated / Path(filename).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        run(["lean", "--trust=0", "-DwarningAsError=true", "-o", str(target), filename],
            Path(filename).stem + "-strict.log", env)
        artifacts[filename] = target
    report["strict_source_exit_codes"] = {f: 0 for f in SOURCES}
    compiled = {f: digest(p) for f, p in artifacts.items()}
    output = run(["lean", "--trust=0", "-DwarningAsError=true", AUDIT],
                 "complete-types-and-axioms.txt", env)
    assert compiled == {f: digest(p) for f, p in artifacts.items()}
    assert snapshot == {f: digest(f) for f in SOURCES + [AUDIT]}
    report["isolated_fresh_compilation"] = True
    report["audit_exit_code"] = 0
    report["source_sha256"] = snapshot
    report["compiled_artifact_sha256"] = compiled
    assert all(t not in output for t in ["sorryAx", "⋯", "…"])
    assert all(re.search(r"\bdef " + re.escape(n) + r"\b", output) for n in DEFINITIONS)
    report["audited_definition_bodies"] = DEFINITIONS
    found = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
        output, re.S)
    assert len(found) == 1 and found[0][0] == NAME, found
    used = {re.sub(r"\.\{[^}]*\}$", "", s.strip())
            for s in found[0][1].split(",") if s.strip()}
    assert used <= ALLOWED, used
    report["axioms"] = {NAME: sorted(used)}
    compressed = gzip.compress(output.encode(), mtime=0)
    assert gzip.decompress(compressed) == output.encode()
    artifact = Path("verification/zero-center-obstruction-types-and-axioms.txt.gz")
    artifact.write_bytes(compressed)
    report["complete_type_output_artifact"] = str(artifact)
    report["compressed_output_sha256"] = digest(artifact)
    report["complete_type_output_sha256"] = hashlib.sha256(output.encode()).hexdigest()
    report["complete_type_output_bytes"] = len(output.encode())
    report["compressed_output_bytes"] = len(compressed)
    report["scope"] = (
        "Explicit six-dimensional Hamilton model: skew J with J^2=-I, symmetric L, "
        "an explicit quadratic form with one negative square, real eigenvectors with "
        "eigenvalues +1 and -1, an exactly identified two-dimensional kernel, and "
        "coercivity on the reference centre, but no invariant zero-centre graph "
        "and no commuting bounded retraction onto the kernel. This refutes the "
        "general static-coercivity-to-splitting inference only; actual Hartree "
        "graph/domain/spectral obligations remain open."
    )
    report["validation_passed"] = True
except Exception as error:
    report["error"] = repr(error)

Path("verification/zero-center-obstruction-status.json").write_text(
    json.dumps(report, indent=2, ensure_ascii=False) + "\n")
print(json.dumps(report, indent=2, ensure_ascii=False))
raise SystemExit(0 if report["validation_passed"] else 1)
