# HBL revised §2.13 — same-source physical Kummer C¹ main-chain audit (2026-11-08)

## Manuscript scope and counting

Revised 13-environment manuscript: **11/13 (84.62%)**, with §2.13 and the final Type-II existence/dynamical-rate theorem still OPEN.
Historical original and historical 21-environment counts are distinct. Auxiliary Lean compilation successes cannot increment the numerator.

Immutable target: a genuine radial 3D energy-critical inverse-square quartic Hartree Type-II strong solution with dynamically selected blow-up exponent, **not an assumed rate**. The shortened §2.13 target is **one genuine fixed-order physical parametrix with O(s^(-9/4)) center/threshold residual and direct parameter Lipschitz control**.

## Newly strictly accepted source-selected chain

1. **Actual source → unique compatible real speed → original Green upper Kummer value/slope → time-decaying compact repair.**
   - Source: `HBL/TypeIIDynamicSelection/ActualHartreeSelectedKummerRepairSourceTimeGain.lean`
   - Commit: `a36358c1d1dbe898643735e28a9e45621371d2d6`
   - Strict CI: https://github.com/penghongzhong/HBL/actions/runs/42431931379 — **success**.
   - `actual_Hartree_selected_physical_Kummer_repair_from_source_order`.
   - Same original weighted source controls the actual selected jet, then the genuine sqrt clock gives `||H_outer(s,r)|| <= C s^(-delta) bubble(r)`, with no independent upper-jet decay hypothesis.

2. **Same origin Green source, globally spliced 3-piece physical field: C¹ interface derivatives, exact frozen scaled Kummer operator in three open regions, and radial Hdot¹ energy of its replacement annulus.**
   - Sources: `ActualHartreePhysicalKummerC1Splice.lean`, `ActualHartreePhysicalKummerC1PDEH1.lean`.
   - Strict CI: https://github.com/penghongzhong/HBL/actions/runs/42431440792 and https://github.com/penghongzhong/HBL/actions/runs/42431440790 — both **success**.

3. **One selected speed/one adjusted source/one Kummer field, combining items (1)–(2).**
   - Source: `HBL/TypeIIDynamicSelection/ActualHartreeSelectedKummerThreeRegionC1SourceBridge.lean`.
   - Commit: `25d538ad13a774c3bc4c035d708cf6e91cca3888`.
   - Strict CI: https://github.com/penghongzhong/HBL/actions/runs/42434299948 — **success**.
   - `actual_Hartree_selected_source_Kummer_three_region_C1_PDE_and_H1`.

4. **Removing the independent continuity premise on the *adjusted* Kummer forcing** (under stricter, physically meaningful regularity of the original forcing):
   - `ActualHartreeAdjustedKummerSourceContinuity.lean`, commit `8e1b5090297c6f27f82c6773e41a8641fa9d9d19`; dedicated CI https://github.com/penghongzhong/HBL/actions/runs/42435689620 **pending success at this checkpoint**.
   - Strengthened integrated statement, commit `c3ecc6c254a37d6c714f6e69cd9010a76f518fc1`; CI https://github.com/penghongzhong/HBL/actions/runs/42435748242 **pending success at this checkpoint**.
   - Do not treat a pending CI as accepted.

## Explicit remaining mathematical gap, not just a build gap

The selected C¹ three-piece field consists of an interior origin-normalized Green branch, an interface-repair annulus, and zero outer continuation. **Its full nonlinear Hartree residual is not equal to the residual of the indicator-supported outer repair tail alone**. Existing successful finite-core nonlinear PDE telescoping for `actualKummerFinitePhysicalTail` applies to compact moving tails, not automatically to the full globally spliced field.

To close the fixed-order revised §2.13 target, prove, on one actual modulation orbit:

1. One time-dependent selected compatibility path and sufficient parameter/time regularity of its source, source-selected Green branch and upper jets; **do not infer these from separate fixed-slice existence statements**.
2. The exact full Hartree nonlocal interactions of the *complete* spliced/inner/remote physical profile, including all cross quartic density products, actual moving-interface transport and the true physical time derivative.
3. Genuine inner-plus-annulus-plus-remote radial Hdot¹ energy and source norms for those same fields, not just annular repair energy.
4. An actual positive **relative** residual-order step `R_j -> R_(j+1)` in the manuscript's weighted source norm, then finitely many real steps until uniform `O(s^(-9/4))` in the center/threshold inputs.
5. Direct `s^(-9/4)` threshold-source Lipschitz control under both varying compatibility columns, followed by true PDE shooting and dynamically selected rate.

The accepted strict CI results above are valid subtheorems; none of them alone establishes a whole three-region Hartree parametrix. New mathematical source bounds must not be inserted as packet fields, dummy `GeneratedTerm.order`, or new main-theorem hypotheses.

## Audit policy

Lean 4.35.0-rc3; pinned Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
Dedicated strict builds use `--trust=0`, warningAsError and `#print axioms`; preserve build artifacts and audit log. Check no `sorryAx`, `admit`, new axioms, or hidden replacement of a needed original-PDE producer. The exact paper theorem and formal statement must be matched before increasing 11/13.


## 2026-11-08 subsequent strict acceptance and next two source-faithful producers

Strict results independently verified:
- Stronger *original-source-continuity-only* selected C1 Kummer source theorem: `42435748242` **success**, commit `c3ecc6c254a37d6c714f6e69cd9010a76f518fc1`. Dedicated adjusted-source continuity: `42435689620` **success**.
- Exact nonlinearly telescoped residual of the moving complete Green–repair–zero Kummer fields, with actual two C1 junctions: `42436411714` **success**, commit `9fce9a9ba22b3865523e1df9c286bb291980f60c`. This proves an *identity*, not an `s^(-9/4)` norm bound.

New unaccepted main-chain candidates (do NOT count before successful strict replay):
1. `HBL/TypeIIDynamicSelection/ActualHartreeMatchedKummerInteriorSourceBound.lean`, commit `80f8da751c799e001674b13c7ddede0880241118`, CI https://github.com/penghongzhong/HBL/actions/runs/42438443690. Proves that after genuine obstruction cancellation the interior Green and regular Kummer field is controlled by the source norm and actual LEFT Fredholm jet, not an independent regular homogeneous amplitude:
   `||w(r)|| + ||w'(r)|| <= 2 C^3 ((b-a) M + ||U|| + ||DU||)` on `r in [a,b]`.
   This is currently a fixed-annulus estimate with explicitly visible `OriginBasisOn K a b C`. A time-uniform control on shrinking left interfaces remains a NONTRIVIAL outstanding analytic requirement.
2. `HBL/TypeIIDynamicSelection/ActualHartreeInnerKummerRepairFourPieceC1.lean`, commit `b4086ab71708a634b50b8e74c6bb36fe6f05c481`, CI https://github.com/penghongzhong/HBL/actions/runs/42438690207. Joins the ACTUAL normalized Fredholm inner field at `L` to the same-source Kummer Green continuation on `(L,aB]`, its physical repair on `(aB,2aB]`, and zero beyond. It targets all THREE value/derivative matching joins, not merely the separate Green–repair–zero field.

Next indispensable bridge: put the ORIGINAL time-dependent 3D Hartree PDE residual on this *inner–Green–repair–remote* global field, including dynamic moving endpoints, original nonlocal quartic interactions, genuine radial Hdot1 energy in the inner/Green/remote regions, and gain estimates relative to the prior full physical residual. Then obtain the uniform fixed `O(s^(-9/4))` residual and threshold-coordinate Lipschitz bound. Do not equate the older indicator-tail core gain with the full-field residual.

Formal revised manuscript numerator remains **11/13 (84.62%)**. The final Type-II blowup exponent must still be derived dynamically from the actual Hartree orbit; no a priori rate assumption is permitted.
