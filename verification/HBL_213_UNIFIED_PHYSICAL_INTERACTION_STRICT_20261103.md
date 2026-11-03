# HBL revised 2.13: one real physical Hartree nonlinear interaction — strict accepted source

- Audited source commit: `5c94fa3ed34316e2602a59db0c92a5d0d0c860c5`.
- GitHub Actions: https://github.com/penghongzhong/HBL/actions/runs/41608607915 — **completed/success**, dedicated strict joint build and axiom audit.
- Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, `--trust=0`, `-DwarningAsError=true`.
- Main theorem: `HBL.TypeIIDynamicSelection.actual_Hartree_one_radiation_full_nonlinear_source_gain`.
- File: `HBL/TypeIIDynamicSelection/ActualHartreeOnePhysicalNonlinearSourceGain.lean`; corresponding `Audit.lean` prints full exported theorem type and transitive axioms.
- The strictly successful workflow rejects `sorry`, `admit`, `axiom`, `native_decide` and `unsafe` in the checked source modules, and audits only standard kernel axioms `propext`, `Classical.choice`, `Quot.sound`.

## Exactly proved

For a single actual radial physical regular radiation field `z`, its genuine 3D inverse-square quartic moment, scaled `Z_ell`, and the original moment-selected moving monopole `V_c`, the same nonlocal Hartree PDE interaction splits into all four terms:
`P_mix*C(V) + P_mix*(C(V+Z)-C(V)) + P_pure*(C(V+Z)-C(Z)) + P_core*(C(V+Z)-C(V))`, where the actual quartic Riesz potentials and actual complex cubic are retained.

The conjunction gives:
1. Actual core potential minus `3*W^2` is `O(ell)` under the explicit moment and small-scale conditions.
2. Full pure-radiation quartic Riesz potential is `O(ell)`.
3. The complete mixed quartic Riesz potential is `O(sqrt(ell)/(1+r))`.
4. The pure-radiation potential times the *changed* complex cubic obeys the exact Lipschitz source estimate.
5. The full physical source split is an equality, with a direct verified real-to-complex quartic identification.

## Boundaries

The theorem states its physical radial measurability, Strauss and L-infinity bounds, bounded quartic moment, and small scale explicitly. The separate cited PDE local theory must provide these conditions for the selected orbit. This theorem does **not** construct a Type-II orbit, derive its rate, prove all weighted Fredholm \(L^2\) source estimates, verify the exact inner/Kummer/remote \(C^1\) matching, or realize the abstract finite-profile source packet from that orbit.

Two sharper core/pure spatial Riesz potential lemmas and a mathematically reduced three-envelope full nonlinear source weighted bound have been submitted for independent further verification. They are not accepted until strict CI success.

**Revised numbered manuscript: 11/13 accepted. Revised 2.13 and the dynamical Type-II main theorem remain OPEN. Historical original counts unchanged.**
