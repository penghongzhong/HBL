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


## 2026-11-08 next actual Green load-bearing acceptance

**Strict source → interior Green field:** CI https://github.com/penghongzhong/HBL/actions/runs/42439861649 SUCCESS, theorem `actual_Hartree_matched_Kummer_interior_from_source_and_left_jet`. It proves the genuine matched origin Green value and slope across a fixed annulus, source-plus-Fredholm-jet controlled. Its `OriginBasisOn K a b C` budget is **not automatically uniform** as `a=L/scale` moves towards zero.

**Strict physical Green radial energy:** CI https://github.com/penghongzhong/HBL/actions/runs/42440742250 SUCCESS, theorem `actual_Hartree_matched_physical_Green_region_radial_H1_energy`. Integrates the real physical 3D weight `y^2` over `[A*a,A*b]` using the ORIGINAL Green source, not an abstract H1 packet.

**Strict physical Green bubble envelope:** CI https://github.com/penghongzhong/HBL/actions/runs/42440955622 SUCCESS, theorem `actual_Hartree_matched_physical_Green_bubble_from_source`. Proves `||v(y)|| <= (1+A*b)*E*bubble(y)`, with `E=2*C^3*((b-a)*M+||U||+||DU||)`. C is still the original fixed-annulus budget.

**Both TRUE Hartree Wronskian source Green coefficients at EVERY radius of the moving interval**: CI https://github.com/penghongzhong/HBL/actions/runs/42441060509 SUCCESS for `actual_Hartree_scaled_Kummer_both_Green_coefficients_uniform`. Both original normalized source integrals are controlled by `(8/3)*G*Cphys*ell^(1/8)*L^(-3/8)`; neither coefficient has a positive extra power of physical Kummer scale. `G` is the explicitly assumed uniform `K.y,K.dy,K.x,K.dx` solution budget. This is **not** yet a time-uniform full physical field bound after multiplication by the singular fundamental solution.

**New CI candidates, not yet counted:**
- Full **Fredholm inner–Kummer Green–repair–zero** physical three C¹ joins, commit `e1d516885bd7edc30e2b503e3a7a17040133e8a7`, CI https://github.com/penghongzhong/HBL/actions/runs/42441307918.
- Exact **compatible singular Green source-moment transport** `A(r)=J_-(r0)-∫_{r0}^r (X F/W)`, commit `fec65b97486c1429e39ec8b8084d21eb41204a81`, CI https://github.com/penghongzhong/HBL/actions/runs/42441241401.
- Genuine **regular origin mode+exact Wronskian** projection `||J_-(r0)|| <= C_reg*r0*(||U||+r0||DU||)`, commit `ec689c2cc052085ca0c5dbfaab2a5c1cba8087b3`, CI https://github.com/penghongzhong/HBL/actions/runs/42441530145.
- Combined **original two-channel Fredholm source → outgoing trace with an r0 gain** (no independent left jet), commit `d7693be6cbea5ef5573bfe607a807dd5bcd97d6d`, CI https://github.com/penghongzhong/HBL/actions/runs/42441627000.
- **Actual near-inner-interface local Hartree Green source moment vanishing linearly at r=r0**, commit `5293bf6c1370ba28ca9456f3646b42b7d87dffd4`, CI https://github.com/penghongzhong/HBL/actions/runs/42441909936.

Mathematical manuscript derivation is synchronized in `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`; CI-pending claims therein are explicitly labelled candidates.

**The remaining §2.13 gate is unchanged:** assemble the SAME actual time-dependent inner/Green/repair/remote correction in original 3D Hartree PDE, derive true moving interface/time-parameter derivative and all quartic nonlocal cross-region source estimates as a genuine relative residual-order increment, prove time-uniform weighted center/threshold `O(s^(-9/4))` and direct two-coordinate Lipschitz, then strict-replay the whole revised theorem statement. The final Type-II speed exponent is an output of the PDE orbit, never a rate hypothesis. **Revised original environment count: 11/13 (84.62%).**


## November 8 formal acceptance update — verified source-to-C1 chain

Strictly accepted at the pinned Lean/Mathlib kernel (dedicated CI):

- **Genuine compatible singular Green moment transport** `actual_Hartree_compatible_singular_Green_coefficient_local_transport` and full matched expression: [42442134533](https://github.com/penghongzhong/HBL/actions/runs/42442134533) — **SUCCESS**.
- **Actual original Wronskian outgoing trace radius gain** `actual_Hartree_origin_outgoing_trace_without_inverse_radius_loss`: [42447225839](https://github.com/penghongzhong/HBL/actions/runs/42447225839) — **SUCCESS**.
- **True two-channel Fredholm source → trace radius gain** `actual_Hartree_original_Fredholm_outgoing_trace_source_radius_gain`: [42447225916](https://github.com/penghongzhong/HBL/actions/runs/42447225916) — **SUCCESS**.
- **Full physical four-piece Fredholm/Green/repair/zero C¹ at three interfaces** `actual_Hartree_inner_Kummer_four_piece_three_C1_joins`: [42447225879](https://github.com/penghongzhong/HBL/actions/runs/42447225879) — **SUCCESS**.

The revised **11/13 (84.62%)** count remains unchanged: each success is a load-bearing auxiliary proof, not yet the **whole** retained manuscript §2.13 physical parametrix or final dynamical Type-II blowup theorem. The true full nonlinear same-orbit weighted residual `O(s^(-9/4))` and threshold Lipschitz are open.

New strict CI candidates not yet accepted at this checkpoint:
- Original Hartree local source moment: branch commit `2980bcc437bf4762bdd57a5d92dae96fedb8c028`; CI [42447752525](https://github.com/penghongzhong/HBL/actions/runs/42447752525).
- Regular-origin improved `|X|=O(1)` times singular physical Green source integral, **scale-free** `O(C_reg*G*C_phys*ell^(1/8))`: [42447752489](https://github.com/penghongzhong/HBL/actions/runs/42447752489).
- Fully compatible source and original Fredholm trace on the singular physical Green branch: [42447752505](https://github.com/penghongzhong/HBL/actions/runs/42447752505).

Crucial quantifier distinction: the latter two conditional candidate statements explicitly assume exact compatibility of the **same original complex Hartree source**. The existing unique Cramer-speed producer supplies compatibility for its own *adjusted* source; those must be identified before claiming unconditional one-orbit construction. No new fixed-rate assumption may enter.
