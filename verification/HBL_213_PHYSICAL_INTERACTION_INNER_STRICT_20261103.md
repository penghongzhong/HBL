# HBL 2.13: complete physical interaction to the original inner Fredholm correction

## Strict acceptance

- Dedicated run: https://github.com/penghongzhong/HBL/actions/runs/41647608340 — **completed/success**.
- Audited commit: `3d7d7e01cbb082a0012dce28d2d3eaf36fde8386`.
- Lean `4.35.0-rc3`; Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Complete Lake build: **4046 jobs**.
- Source and separate audit passed `--trust=0 -DwarningAsError=true`.
- Full declarations and transitive axioms were checked. Only `propext`, `Classical.choice`, `Quot.sound`; no sorry, admit, new axiom, unsafe or native_decide.
- Artifact `13236410680`, SHA-256 `7feb486154e593c1a986336b11387e1553aa8ff88e5a368794c466ada6bfe440` was downloaded and its actual audit log, commit and dependency pin inspected.

Files: `HBL/TypeIIDynamicSelection/ActualHartreePhysicalInteractionInnerSolve.lean` and its `Audit.lean`.

Audited declarations:

1. `actual_Hartree_physical_interaction_inner_channels`.
2. `actual_Hartree_physical_interaction_inner_solve_from_radiation`.

## Actual mathematical scope

The forcing is the complete original Hartree core/radiation interaction `actualHartreePhysicalSliceInteraction ell c z`, not an arbitrary source. Assumptions are exactly `0<ell<=1`, `|c|<=1`, measurable physical radiation, and its nonnegative amplitude/Strauss bounds B,A.

The proof first CALLS the already strictly verified physical weighted source theorem. It derives both real and imaginary `InWeightedL2 (7/4)` inputs. It then uses the original concrete affine and Birman–Schwinger operators to obtain:

- the forced charges `actualPlusCharge (Re F)` and `actualMinusCharge (Im F)`;
- their genuine resonance orthogonality, including pairing integrability;
- zero resonance pairings of both actual affine-corrected sources;
- a unique pair in `InnerCorrections`, each component normalized in the orthogonal complement of its physical Fredholm kernel, satisfying the actual two weighted Fredholm equations.

There is **no** assumed weighted-source bound, freely selected charge, or assumed Fredholm compatibility in the exported physical theorem. Weighted membership occurs as an existentially produced proof, not an input hypothesis.

## Boundaries that remain open

This theorem is for the **interaction contribution** to the inner correction. It does not absorb all transport, phase, modulation, cutoff or higher-profile terms of the common PDE residual. It proves a Hilbert/Fredholm solution, not yet a classical C1 interface realization or an estimate for all endpoint traces.

The same physical source must still be used to construct the actual coupled inner/Kummer/remote corrections, establish the outer compatibility or a proved replacement parametrix, and verify positive time-order gain for every generated residual before invoking finite-profile recursion. No Type-II time law is assumed or obtained here.

**Revised manuscript count remains 11/13 (84.62%).** This is an accepted supporting composition, not acceptance of the whole retained environment 2.13.
