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


## Full moving four-piece Hartree PDE and scale-free Green physical source — next kernel checks

**Submitted exact full-field nonlinear PDE telescope:** commit `348052e75b258f80350ffdea99d2895638ba9a4a`, strict CI [42448073193](https://github.com/penghongzhong/HBL/actions/runs/42448073193) **pending acceptance**. `ActualHartreeFullFourPieceFinitePDETelescoping.lean` instantiates each time-dependent correction as the ACTUAL four-piece `Fredholm inner → origin Green → physical repair → zero` field. The completely nonlocal nonlinear Hartree residual difference is telescoped on literal sums, rather than mistaking a disjoint outer indicator tail for the full field. This proves only exact residual algebra, not a gain.

**Submitted new scale-free singular physical product:** commit `263b35380f30e11bb3bb59f62caef59a50b0baf2`, strict CI [42448233031](https://github.com/penghongzhong/HBL/actions/runs/42448233031) **pending acceptance**. The true regular origin basis estimate `|X(r)|≤1+(D+1)G R²`, original inverse Wronskian `|W(r)⁻¹|=r²` and real physical quartic Hartree source `|S(y)|≤M(1+y)^(-19/8)` imply the pointwise density `|XF/W|≤Creg M` on `ar≥L≥1`. Hence the genuine source moment is `O(Creg M (r-L/a))` and its PRODUCT with the singular origin basis is `O(G*Creg*M)`: **no power of moving scale a remains**. This directly corrects the unnecessary `a`-loss from the coarse `|X(r)|≤G/r` route. The original Hartree amplitude `M=C_phys ell^(1/8)` has a verified positive power of ell; do not silently promote this to `s^(-9/4)`.

**Submitted full compatible-source quantitative physical singular channel:** commit `ad4aa7ff54eabddb3356ea0446d04a172572b354`, revised compatible-basis commit `a72da3da378312768f07815b4e93b45d8f4baf7c`, strict CI [42448233187](https://github.com/penghongzhong/HBL/actions/runs/42448233187) **pending acceptance**. This combines the already accepted singular coefficient transport, original two-channel Fredholm source→Wronskian radius gain, and the scale-free physical source moment. The original exact compatibility hypothesis **is explicit** and must still be generated from the SAME speed-corrected, time-dependent physical Hartree source. Do not substitute compatibility for the unadjusted base source without proving equivalence.

All three proofs are built without `sorry`, `admit` or added axioms. They must pass their indicated dedicated strict CI AND full original statement scope to qualify. **Formal revised count remains 11/13 (84.62%)**. The remaining nonalgebraic obstruction is the true same-orbit source/selected-speed identification plus full time derivative and all nonlocal cross-density contributions in the weighted, Lipschitz-controlled `O(s^(-9/4))` residual.

## 2026-11-08 genuine Riesz source → unique speed / upper-jet candidates

New source-faithful specialization `ActualHartreeTrueSourceSpeedSelection.lean`, commit `25cb679d6138de769f1bbac45f85fe296bbb1bcd`, strict CI [42449888073](https://github.com/penghongzhong/HBL/actions/runs/42449888073), **pending**. It derives the selector's `F ∈ IntervalIntegrable` and `||F(r)|| ≤ Q/r²` directly from the original full physical Hartree Riesz source, with `Q=Cphys ell^(1/8)`. The original unique Cramer real-speed theorem then provides `|p_b|+|p_omega|≤C/a*(N_F+Q)` for the actual source on each admissible annular slice. The annulus ordering `L/a≤B` is explicit, not a Type-II rate assumption.

The companion `ActualHartreeTrueSourceSelectedUpperJet.lean`, commit `8d91cf94566f6cb1c85ac9c956a7ebc6f9dddeb8`, strict CI [42450166551](https://github.com/penghongzhong/HBL/actions/runs/42450166551), **pending**. It also derives the true regular Green coefficient from the original Hartree source, rather than postulating a `Kreg` bound, and supplies the selected physical normalized upper value/slope.

The true regular origin homogeneous coefficient has a separate source-to-amplitude **candidate**, `ActualHartreeRegularOriginCoefficientSourceBound.lean`, commit `8e5532501a6f452dba4b2aefcf7c5a24dc4c9d07`, strict CI [42450013151](https://github.com/penghongzhong/HBL/actions/runs/42450013151), **pending**. Target `||gamma|| ≤ 2G*(||U||+r0||DU||) ≤ 2G*C_F*N_F`, no inverse moving radius.

**Critical PDE scope:** The unique selected speed cancels the compatibility condition of the adjusted source `F0-p_b S_b-p_omega S_omega`, not of the unadjusted physical source `F0`. Previously accepted conditional singular Green estimates with `hzero` imposed for the unadjusted source cannot be substituted without a separately verified producer connecting the adjusted source to the actual selected speed. Original revised environments remain **11/13** until the full same-orbit `O(s^(-9/4))` and threshold Lipschitz are strictly established.


## 2026-11-08 strict CI acceptance and selected-speed physical Green interface (latest)

**New strict kernel successes (replace earlier 'pending' labels):**
- `actual_Hartree_true_nonlocal_source_selects_unique_real_speed` on the ORIGINAL full inverse-square quartic Hartree Riesz source, with real two-channel compatibility and `|p_1|+|p_2| ≤ C/a(N_F+Q)`: [42449888073](https://github.com/penghongzhong/HBL/actions/runs/42449888073) **SUCCESS**.
- `actual_Hartree_singular_Green_local_moment_full_product_gain` for the TRUE baseline Hartree source, with the physical singular basis multiplied back and no moving-`a` loss: [42450195229](https://github.com/penghongzhong/HBL/actions/runs/42450195229) and [42450323793](https://github.com/penghongzhong/HBL/actions/runs/42450323793) **SUCCESS**.
- `actual_Hartree_finite_original_Fredholm_four_piece_PDE_telescopes`, exact nonlinear four-piece Fredholm/Green/repair/zero Hartree residual identity: [42448073193](https://github.com/penghongzhong/HBL/actions/runs/42448073193) **SUCCESS**. This is an exact telescoping identity, NOT a full weighted estimate.

**New true speed-correction source subchain (strict CI pending at this checkpoint):**
- `ActualHartreeSelectedSpeedSingularGreenGain.lean`, [commit e8d15da](https://github.com/penghongzhong/HBL/commit/e8d15dafb6a001f529b92a7e8e4a0cd9616c08c3), [CI 42450807652](https://github.com/penghongzhong/HBL/actions/runs/42450807652): derives `||Y(r) A_{speed}(r)|| ≤ G² C_s a (|p_1|+|p_2|)` from the genuine speed source `S_b,S_omega=O(a/r)`, not the baseline source's `(1+ar)^(-19/8)` tail.
- `ActualHartreeSelectedSpeedPhysicalGreenNoScale.lean`, [commit c50a7ad](https://github.com/penghongzhong/HBL/commit/c50a7ade6b664ceed37da3b9d204d1d235b6f411), [CI 42450891480](https://github.com/penghongzhong/HBL/actions/runs/42450891480): composes the strict original-source unique selector and the physical speed-product bound for the SAME `p`; expected result `||Y A_{speed}|| ≤ G² C_s C(N_F+Q)`, with no `a` or `1/a` loss. **Do not count until CI Success.**
- The exact derivation is synchronized to `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`.

**One rejected interpretation:** The corrected Green source is `F_o=F_0-p_bS_b-p_omega S_omega`; the high-decay `F_0` bound is NOT valid for the speed components separately. Decomposition into the verified physical baseline `Y A_{F_0}` and the speed products is mandatory. All resulting terms must be attached to the same actual speed-selected, time-dependent physical profile, and the full Hartree `O(s^(-9/4))` residual and threshold Lipschitz remain open.

**Revised manuscript environment count remains 11/13 (84.62%).** The fixed-order §2.13 single-orbit parametrix and the final dynamically derived Type-II blowup theorem are NOT yet accepted. Earlier branch-specific successful CI modules do not convert a conditional full-PDE source smallness assumption into a proved original environment.


## 2026-11-08 genuine selected Green main-chain continuation (verified checkpoint)

- **STRICT SUCCESS:** original nonlocal Hartree source → unique real two-speed, [CI 42449888073](https://github.com/penghongzhong/HBL/actions/runs/42449888073).
- **STRICT SUCCESS:** true Hartree local singular Green physical product without matching-scale loss, [CI 42450195229](https://github.com/penghongzhong/HBL/actions/runs/42450195229).
- **STRICT SUCCESS:** same genuine selected speed, its physical singular Green correction and original source selected-speed bound **jointly**; [CI 42453696842](https://github.com/penghongzhong/HBL/actions/runs/42453696842), repaired commit 378783e. Exact statement: ActualHartreeSelectedSpeedPhysicalGreenNoScale.lean. No additional moving-scale factor.
- **STRICT SUCCESS from existing branch:** same source → adjusted compatible outgoing Green transport [CI 42451487366](https://github.com/penghongzhong/HBL/actions/runs/42451487366); same selected-speed full inner/Green/repair/zero three-interface C1 field [CI 42451545608](https://github.com/penghongzhong/HBL/actions/runs/42451545608).

**Recent candidate/accepted auxiliary proofs (only full revised manuscript environments increment numerator):**
1. **STRICT SUCCESS** ActualHartreeTrueSourceSelectedAdjustedLocalGreenNoScale.lean, original commit dffbae9, tactic repair 58933d7. Original CI [42453950339](https://github.com/penghongzhong/HBL/actions/runs/42453950339) failed on a no-op dsimp at line 121; corrected CI [42454972883](https://github.com/penghongzhong/HBL/actions/runs/42454972883) **SUCCESS**. Full original F0 minus both selected modulation sources controls the local physical singular Green product, with no positive a-loss. Accepted auxiliary only; environment count unchanged.
2. ActualHartreeTrueSourceSelectedFullSingularGreenGain.lean, commit 047fc66. CI [42454285470](https://github.com/penghongzhong/HBL/actions/runs/42454285470) failed from old local dependency; CI [42454972909](https://github.com/penghongzhong/HBL/actions/runs/42454972909) reached the new module and failed solely on no-op dsimp (line 127); fixed in 5637b71. New strict CI [42455814268](https://github.com/penghongzhong/HBL/actions/runs/42455814268) PENDING, not accepted. Same selector, corrected physical Fredholm jet and full right-endpoint singular Green transport.
3. **STRICT SUCCESS** ActualHartreeTrueSourceSelectedCorrectedNorm.lean, commit d882d6f, CI [42454532669](https://github.com/penghongzhong/HBL/actions/runs/42454532669): genuine Hartree source produces BOTH corrected weighted inner Fredholm norms and the corrected outer envelope, with total bound C_adj * (N_F+Q_H). This is an accepted auxiliary theorem; it does not change 11/13.
4. ActualHartreeTrueSourceSelectedFullSingularOriginalNorm.lean, commits d4e8da4 and 7b6da73 (preemptive no-op tactic removal). First CI [42454628449](https://github.com/penghongzhong/HBL/actions/runs/42454628449) failed due old imported local module; new strict CI [42455841142](https://github.com/penghongzhong/HBL/actions/runs/42455841142) is PENDING, not accepted. Target: eliminate corrected Fredholm norm from full singular Green bound in favor of actual N_F+Q_H.

5. ActualHartreeOnePhysicalSourceFullSelectedSingularGreen.lean, commit 47a907b, first CI [42454937267](https://github.com/penghongzhong/HBL/actions/runs/42454937267) failed from outdated import; corrected dependency run [42455841135](https://github.com/penghongzhong/HBL/actions/runs/42455841135) PENDING. Bind both Fredholm channels and F0 to the same genuine Hartree interaction; source continuity remains explicit.

TeX synchronized in verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex (latest commit f17a373; subsequent strict-status updates may follow).

**Unchanged strict revised 13-environment count: 11/13 = 84.62%.** Neither full dynamical physical Fredholm/Green/repair/remote residual nor O(s^-9/4) positive relative gain and threshold Lipschitz are proved by the fixed-slice Green estimates. Dynamical Type-II exponent must be derived, not assumed.


## 2026-11-08 accelerated joint acceptance and moving-source derivative

- **STRICT SUCCESS:** [CI 42455841135](https://github.com/penghongzhong/HBL/actions/runs/42455841135), ActualHartreeOnePhysicalSourceFullSelectedSingularGreen.lean at commit 7b6da731. Both Fredholm channels and the original outer Riesz source originate in ONE physical quartic Hartree interaction; a unique selected real speed controls the complete right-endpoint singular Green component using only N_F+Cphys*ell^(1/8). Continuity of the original transmission channels remains an explicit premise. Accepted auxiliary only, NOT the full revised §2.13 environment.
- [CI 42455814268](https://github.com/penghongzhong/HBL/actions/runs/42455814268) failed solely on unused theorem-statement let binders hpa/hma. Removed the mathematically redundant hgp,hgm,hpa,hma statement binders without changing the result, commit 89ecbc6d. Replacement [CI 42456627583](https://github.com/penghongzhong/HBL/actions/runs/42456627583) and dependent rechecks 42456627562 / 42456627579 are PENDING. The earlier successful composite applies to its own pinned SHA; it does not prematurely certify the newly revised branch head.
- **NEW CANDIDATE:** ActualHartreeTrueMovingAdjustedSourceDerivative.lean, commit c2ae7be, pinned strict workflow commit 01459ae3, [CI 42456222166](https://github.com/penghongzhong/HBL/actions/runs/42456222166) PENDING. Proves product-rule time differentiation of the genuine time-varying original physical quartic Riesz source with both selected speed directions. The actual Cramer pair's time derivatives and quantitative bound are derived, not inserted. Time-differentiability of original F0,S_b,S_omega and of physical compatibility columns and obstruction remain explicit physical inputs to prove on one PDE orbit; moving Kummer basis and time-dependent full-field residual are not covered.
- TeX synchronized in verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex, commit 626606d.

**Formal revised environment count remains 11/13 = 84.62%.** Outstanding §2.13: genuine one-orbit full four-piece time and original 3D nonlocal cross-density estimates, weighted O(s^(-9/4)) and direct threshold Lipschitz; then final dynamically derived Type-II rate (not prescribed).


### 2026-11-08 audited full singular Green source composite

The following two genuinely new full-component auxiliaries have **STRICT SUCCESS** at commit 7b6da7315e903b57ceb2b35f7cfa1628aea6c39e:

- [42455841142](https://github.com/penghongzhong/HBL/actions/runs/42455841142): actual_Hartree_true_source_selected_full_singular_original_norm_gain; eliminates the adjusted Fredholm norm from the entire right-endpoint singular Green bound.
- [42455841135](https://github.com/penghongzhong/HBL/actions/runs/42455841135): actual_Hartree_one_physical_source_selected_full_singular_Green_gain; instantiates BOTH original Fredholm channels and the outer Kummer source from ONE genuine 3D inverse-square quartic Hartree interaction.

Independently retrieved the archived audit.log, strict.log, source hash, and pinned compiler-version outputs of BOTH runs. In each, strict.log is empty, no sorryAx is present, and #print axioms has **exactly [propext, Classical.choice, Quot.sound]**. No extra axioms were introduced in the proof dependence. The earlier independent upstream lint error was removed in commit 89ecbc6d; that modified parent declaration needs its OWN replacement CI 42456627583, still pending here. This does not establish time differentiation or the O(s^(-9/4)) four-piece PDE residual. Formal count remains 11/13.


### Strict triad all at revision 89ecbc6d, after independent audit

Full true-source singular Green derivative-free chain is now strictly reaccepted on SAME source revision 89ecbc6d:
- 42456627583 SUCCESS: true source and compatible full right-endpoint singular Green.
- 42456627562 SUCCESS: elimination of adjusted Fredholm norm, original N_F+Cphys*ell^(1/8) only.
- 42456627579 SUCCESS: both weighted inner channels plus outer source instantiated from the SAME original quartic Hartree nonlocal physical expression.

This eliminates the strict unused-binder warning, not an additional mathematical hypothesis. Thus the standalone and dependent compositional modules are all currently successful on a common SHA. None supplies the time differentiability of the complete C1 four-piece field or O(s^-9/4) full 3D Hartree residual.

The first moving original-source derivative CI 42456222166 failed a term-level let/negative-source Lean parse ambiguity (no theorem accepted); fixed in fc786e1. Both corrected 42457157758 (moving physical source derivative) and 42457157917 (dominated true-source regular Green integral derivative) remain STRICT CI PENDING at this checkpoint. Their explicit source derivatives and majorant still require original PDE estimates.

Speed optimization experiment: workflow .github/workflows/hbl-true-source-selected-speed-green-no-scale.yml now includes a nonblocking pinned shared Lake build cache SAVE step, commit 973c46d, CI 42457325903. The existing strict workflows already use compatible restore prefixes; acceleration is provisional until cache upload succeeds.

### Moving-source post-compile correction

CI 42457157917 failed on an ordinary Lean conversion between pointwise `fun t =>` and the function-level `Pi.sub`/`Pi.mul` result of HasDerivAt subtraction/product rules in ActualHartreeTrueMovingAdjustedSourceDerivative.lean:100, not a Hartree estimate or added axiom. Corrected with `Pi.sub_apply` and `Pi.mul_apply`, commit c9a598959f29222372250de68c5af4175e4e1c6c. Strict new runs 42458002571 (moving original source derivative) and 42458002671 (moving regular Green derivative) are IN PROGRESS, not accepted. TeX synced commit 3099cdf4.

The full selected Green source/adjusted-norm/original physical-source CI triad 42456627583 / 42456627562 / 42456627579 remains STRICT SUCCESS at same earlier SHA 89ecbc6d. No change to 11/13.


## 2026-11-08 moving Hartree source and actual Green endpoint — strict acceptance

1. **STRICT SUCCESS:** [CI 42458168170](https://github.com/penghongzhong/HBL/actions/runs/42458168170) at commit 3e278d00b1b022e83c7d487aec967182997ab7e8, ActualHartreeTrueMovingAdjustedSourceDerivative.lean. Differentiates the genuine evolving F0(s,r) - pb(s) Sb(s,r) - pw(s) Sw(s,r), deriving pb',pw' from the actual Cramer pair and retaining all three physical source derivative contributions. Source and compatibility-data differentiability remain explicit premises, not produced from measurable radiation.

2. **STRICT SUCCESS:** [CI 42465956550](https://github.com/penghongzhong/HBL/actions/runs/42465956550) at commit 2fdd446d3e3bcf8a82194f39f2566c7f4997842d, ActualHartreeTrueMovingSelectedRegularGreenDerivative.lean. By the existing dominated parametric interval integral theorem, the ORIGINAL regular Green coefficient has the true source-time derivative when the original evolving Hartree source and its selected real speeds satisfy the explicitly stated derivative, dominated-majorant, measurability and integrability hypotheses. The original proof's real/complex derivative casts and unused argument warnings were fixed. The Kummer basis and integration endpoints are frozen only in THIS partial derivative.

3. **STRICT SUCCESS:** [CI 42466055866](https://github.com/penghongzhong/HBL/actions/runs/42466055866) at commit 9f54a713817f354bbb79e9b799c12aba80a32f9a, ActualHartreeSlowInnerMovingGreenEndpoint.lean. The true source-localization radius L(s)=ell(s)^(-1/16) and the physical Kummer interface r0(s)=L(s)/a(s) have derived time derivatives from ell'(s),a'(s), including the original selected source Green lower-endpoint contribution at a fixed source slice. Original forcing continuity is explicit. No Type-II blowup rate is assumed.

Paper synchronization: verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex, updated commit 35c5709.

**Strict scope boundary:** These are three separate, rigorously typed partial derivative theorems, NOT a joint differentiated complete four-piece Hartree field. The latter still requires a genuine joint source/endpoint/basis derivative, actual time-differentiable nonlocal Riesz interaction and full three-dimensional cross-density terms. The fixed-order complete PDE residual O(s^(-9/4)), direct threshold Lipschitz and final derived Type-II exponent remain unproved. Revised manuscript count remains **11/13 (84.62%)**.


## 2026-11-08 physical time budgets: strict no-extra-a-loss acceptance

**Two new strictly accepted load-bearing auxiliary theorems**; neither is counted as the complete §2.13 environment.

1. `ActualHartreeMovingSelectedSourceTimeBudget.lean`, final source `de54e97003620e0793fae1aa80877611b7849260`. Initial compile passed on [CI 42471292372](https://github.com/penghongzhong/HBL/actions/runs/42471292372). The first audit workflow still printed the axioms of an older dependency; that was corrected explicitly in commit `f0cf6ae`. **Exact target strict re-audit [CI 42471590107](https://github.com/penghongzhong/HBL/actions/runs/42471590107): SUCCESS.** The actual Cramer velocity derivative times true speed profiles loses no factor `a^(-1)`. It proves the true, time-varying adjusted original Hartree forcing pointwise estimate with `1024 Cs/(B²r) * ||Z'+p_b b'+p_omega w'||` and explicitly retained physical `F0',Sb',Sw'` terms.

2. `ActualHartreeSelectedSpeedGreenTimeNoScale.lean`, final source `a6155594b8c4ffadbe9b0276ff2a3cacd21f902c`. This combines the original normalized regular Green source integrals `||B_K[S_b]||,||B_K[S_omega]||≤Cs G a B` with the *same actual differentiated real Cramer speed*. The direct time coefficient is bounded by `(1024 Cs G/B)||Z'+p_b b'+p_omega w'||`; the moving scale `a` cancels, no artificial forcing or prescribed Type-II rate. The initial workflow's stale axiom print was corrected in `132efe7`. **Exact-target strict [CI 42471592939](https://github.com/penghongzhong/HBL/actions/runs/42471592939): SUCCESS.**

**Independent archive inspection of BOTH exact-target strict runs:** reproduced Lean version 4.35.0-rc3; target-checked source SHA256 and empty `strict.log`; direct `#print axioms` yields exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, `admit` or added axioms in the target proof dependencies. The 0-error, trust-zero and warnings-as-errors success applies to the audited SHA, not untested later edits.

**Manuscript synced** to `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`, commit `61ed0041`. Both estimates are for the actual moving source and actual regular Green coefficient; they are CONDITIONAL on the explicitly stated differentiability of original physical source and moving compatibility columns/obstruction. The nonlocal Hartree time/source Lipschitz along the PDE orbit, the *joint* moving-source/moving-endpoint/moving-Kummer-basis Green derivative, the full four-piece residual `O(s^(-9/4))`, direct threshold Lipschitz and dynamically DERIVED Type-II exponent remain unproved. **Formal revised environment count remains 11/13 = 84.62%.**


## 2026-11-08 actual source-plus-endpoint Green joint derivative: strict acceptance

The Hartree source and the true normalized Kummer lower endpoint are NO LONGER merely handled by two unrelated partial-derivative proofs. The following are newly strict and exact-target-axiom audited:

1. **STRICT SUCCESS** [CI 42472592872](https://github.com/penghongzhong/HBL/actions/runs/42472592872) at 9cb8afa: ActualHartreeMovingSelectedGreenMixedDifference.lean. For F_t = original nonlocal quartic Hartree forcing corrected by the *same unique real Cramer pair*, r_t=ell(t)^(-1/16)/a(t), prove the exact four-term mixed integral identity, with sharp bound |E(t,s)| ≤ C|t-s||r_t-r_s|. No extra Type-II rate or abstract source.
2. **STRICT SUCCESS** [CI 42473023783](https://github.com/penghongzhong/HBL/actions/runs/42473023783), corrected source 811ef15: ActualHartreeMovingGreenJointDerivative.lean. The full mixed term satisfies HasDerivAt 0, using its ACTUAL integral bound and differentiability of the moving endpoint. The fixed-Kummer-basis Green coefficient therefore has derivative equal to the original source-time derivative plus moving lower-endpoint term. No separate assumption that the mixed term has zero derivative.
3. **STRICT SUCCESS** [CI 42473151794](https://github.com/penghongzhong/HBL/actions/runs/42473151794), source e4ad0e1: ActualHartreeOnePhysicalMovingGreenJoint.lean. Instantiates the joint formula using one original 3D nonlocal Hartree source, one unique real selected speed, one actual slow-inner radius ell(s)^(-1/16)/a(s), and the existing source/endpoint derivative producers. Original Green density integrability and short-interval time-Lipschitz remain explicit analytic assumptions here.
4. **STRICT SUCCESS** [CI 42473401888](https://github.com/penghongzhong/HBL/actions/runs/42473401888), source 2b0858e: ActualHartreeSelectedGreenDensityTimeMVT.lean. By the actual real Mean Value theorem, the Green-density short-time Lipschitz input follows from the full time derivative bound of the SAME original Hartree selected source and a bound on the original Y/W multiplier. The physical source derivative bound is an explicit premise to be produced on the one actual PDE orbit.
5. **STRICT SUCCESS** [CI 42473541248](https://github.com/penghongzhong/HBL/actions/runs/42473541248), source 6242b8c: ActualHartreeOnePhysicalGreenJointFromDerivative.lean. Composes #4 into #3: the previously INDEPENDENT Green-density time-Lipschitz premise is now DERIVED from the actual source's time-derivative envelope. The only remaining time smoothness budget is at the genuine original PDE-source level.

Each accepted target CI uses the fixed Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, --trust=0, warningAsError, exact #check and #print axioms on its own target statement (not a template dependency), with no sorryAx reported. CI success concerns these auxiliary declarations only.

Manuscript mathematics and status synchronized to verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex, commit 7083c6a. **Formal revised 13-environment acceptance remains 11/13 = 84.62%**. Genuine remaining analytic obligations are (i) original nonlocal full Hartree PDE source time derivative and weighted uniform derivative bounds along one orbit, including all Riesz mixed cross-density terms, (ii) the moving Kummer fundamental pair and its spatial-temporal basis derivatives, (iii) all-four-piece Fredholm/Green/repair/remote residual O(s^-9/4), and (iv) direct threshold Lipschitz and final dynamically DERIVED Type-II blowup rate. Do not assume a blowup rate or raise manuscript environment counts on partial green calculus alone.


## 2026-11-08 regular upper Kummer jet: moving Fredholm + joint Green derivative

**STRICT SUCCESS:** [CI 42474096247](https://github.com/penghongzhong/HBL/actions/runs/42474096247), corrected source commit a6db90c, ActualHartreeMovingMatchedRegularUpperJet.lean. This connects THREE previously strict sources of actual mathematics:
(1) the moving Fredholm left Kummer value U(s), slope DU(s) and actual normalized Wronskian determine the source-independent regular homogeneous coefficient beta_reg(s);
(2) the ORIGINAL joint time-varying Green term B_K[F(s)](ell(s)^(-1/16)/a(s),B) has the already proved source-plus-endpoint derivative, including its actual mixed-error cancellation;
(3) the full compatibility-cancelled forced regular coefficient gamma(s)=beta_reg(s)+B_K[F(s)] produces the actual regular upper value X_K(B)gamma(s) and slope X'_K(B)gamma(s).

The checked result derives gamma' and BOTH upper-jet time derivatives from the earlier certified Fredholm-jet and Green derivatives. It does not assume a derivative for gamma as a new independent input. The Kummer basis is frozen in this derivative. The full original PDE residual is not yet proved.

**STRICT SUCCESS** [CI 42474332557](https://github.com/penghongzhong/HBL/actions/runs/42474332557): ActualHartreeOnePhysicalSelectedUpperJetTime.lean, commit 1a3559c. This binds F to one actual 3D inverse-square quartic Hartree source with one unique real selected Cramer speed and r0(s)=ell(s)^(-1/16)/a(s), and uses the source-produced joint Green derivative plus moving Fredholm left jet to derive BOTH true selected regular upper Kummer value and slope time derivatives. The required original physical source-time, dominated-integral and Fredholm left-jet regularity remain explicit premises; the moving Kummer basis and full nonlinear residual remain OPEN. This is a strictly accepted load-bearing auxiliary but is NOT the entire revised §2.13 environment.

Corresponding human-readable formulas and named equation references synchronized in verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex, commit e9ec564. Formal revised manuscript count remains **11/13 (84.62%)**. Next indispensable step is to DERIVE those time and weighted derivative budgets from the same actual nonlocal Hartree PDE orbit and then include the MOVING KUMMER BASIS and full nonlinear four-piece error gain. Neither the final Type-II rate nor the claimed s^-9/4 residual is assumed.


## 2026-11-08 original 3D inverse-square Hartree NONLOCAL time derivative — strict acceptance

New main-chain producers strict at pinned Lean 4.35.0-rc3 / Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, target --trust=0, warningAsError with exact-source SHA and target-theorem axiom audit, no sorryAx:

1. **STRICT SUCCESS** [42474757711](https://github.com/penghongzhong/HBL/actions/runs/42474757711), source 1347213, ActualHartreeRadialRieszTimeDerivative.lean: ORIGINAL fixed-radius logarithmic inverse-square Riesz potential of |z(s,rho)|^4 differentiated under the actual half-line integral, from separately verified REAL/IMAG quartic radiation velocity and a genuine integrable majorant. No assumed derivative of the Riesz potential.
2. **STRICT SUCCESS** [42475283498](https://github.com/penghongzhong/HBL/actions/runs/42475283498), corrected source bfd4dd1, ActualHartreeMixedRieszTimeDerivative.lean: the FULL physical quartic mixed density |V+z|^4-|V|^4-|z|^4 has its derivative derived from real monopole V_s and complex radiation z_s; the complete original logarithmic Riesz integral differentiates under the actual dominated envelope. All cross densities, including at V=0/z=0, are retained.
3. **STRICT SUCCESS** [42475554508](https://github.com/penghongzhong/HBL/actions/runs/42475554508), corrected source 1145e91, ActualHartreeLocalCubicTimeDerivative.lean: the physical complex local C(u)=|u|²u multiplier has exact derivative 2Re(conj(u)u_s)u+|u|²u_s, without assuming u is nonzero.
4. **STRICT SUCCESS** [42475714014](https://github.com/penghongzhong/HBL/actions/runs/42475714014), corrected source 0be0baa, ActualHartreeFullNonlocalInteractionTimeDerivative.lean: the ORIGINAL three Riesz potential / three complex cubic source products have their exact time derivative with all cross multipliers. This producer consumes the separately proved potential derivative inputs; it does NOT assume the derivative of the whole nonlinear interaction.
5. **STRICT SUCCESS** [42475826921](https://github.com/penghongzhong/HBL/actions/runs/42475826921), source a99a060, ActualHartreeFullInteractionTimeFromOrbit.lean: strictly composes items 1–4 on ONE real monopole V(s,r) and ONE complex radiation z(s,r). The full original interaction derivative follows from primitive V_s and z_s, three original logarithmic Riesz kernel integral domination hypotheses and genuine source measurability. None of the three Riesz potential derivatives is separately postulated. Complex radiation differentiability at the fixed observer is explicitly assumed, consistent with the high-regularity physical setting.

**Original source formula:** N_int=P_mix*C(V+z)+P_z*(C(V+z)-C(z))+P_V*(C(V+z)-C(V)), with P_mix=I[|V+z|^4-|V|^4-|z|^4], P_z=I[|z|^4], P_V=I[|V|^4], C(u)=|u|²u. Neither density nor potential is replaced by an arbitrary local forcing packet. TeX derivation and referenced equations synchronized in verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex, commit 93be70d.

**REAL REMAINING BLOCKER:** All currently accepted Riesz and nonlinear-source time derivatives hold at FIXED physical observation radius. We have NOT produced the time-dependent observation chain rule r=a(s)r_K, derivative of the moving original Kummer fundamental pair K(s), or proved weighted O(s^(-9/4)) full physical residual and its direct threshold Lipschitz along the same actual three-dimensional Hartree PDE orbit. Primitive time C1 and domination premises still require concrete high-regularity Hartree dynamics (standard published local theory may be cited, but must never be used to assume the needed global matching theorem). No Type-II concentration rate is prescribed.

**Formal revised 13-environment count stays 11/13 (84.62%).** The complete §2.13 physical parametrix and the final dynamically derived Type-II blowup theorem remain OPEN. Auxiliary strict successes do not increment the manuscript environment tally.


## 2026-11-08 original 3D kernel and moving physical observation (strict)

This step reuses three genuine earlier analytic producers:
- HBL/HartreeSpatialCore.lean differentiates the ORIGINAL three-dimensional inverse-square kernel convolution by transferring spatial derivatives to the density instead of differentiating the singular kernel;
- HBL/HartreeSpatialCompletion.lean extends the spatial Frechet derivative from smooth compact density approximants to a noncompact density/gradient under explicit simultaneous L1 and uniform convergence hypotheses;
- HBL/HartreeQuarticGradient.lean derives the quartic density gradient and its L1/L∞ budgets directly from an actual complex 3D field f in C1 and L4 with Df in L2 and stated boundedness.

**STRICT SUCCESS:** [42476562067](https://github.com/penghongzhong/HBL/actions/runs/42476562067), source 4d7fbde. ActualHartreeThreeDMovingObserverDerivative.lean specializes genuine 3D quartic density rho_s=|z(s,·)|^4 to the moving observation point x(t)=a(t)x0; the spatial source derivative follows from noncompact core approximation, not a premise about differentiability of the Hartree potential. This first version retains an explicit density-gradient input D.

**STRONGER STRICT SUCCESS:** [42476734964](https://github.com/penghongzhong/HBL/actions/runs/42476734964), enhanced source 3218ca9 and exact theorem-axiom workflow a962e99. The theorem actual_Hartree_threeD_quartic_moving_observer_from_field eliminates the independently specified density gradient D by applying the earlier original quartic-gradient theorem to f=z(s,·) and establishes

  d/dt P3[|z(s)|^4](a(t)x0)|_{t=s}
    = grad P3[|z(s)|^4](a(s)x0)[a'(s)x0],

where grad P3 is the original convolution against the differentiated **actual physical quartic density**. The noncompact smooth-core approximation (both L1 and uniform convergence of density and gradient) remains an explicit regularity premise, not a consequence claimed for general energy-class data.

TeX derivation and equation references synchronized to verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex, commit a363ea6.

**Important strict scope boundary:** The exact 3D inverse-square convolution and the original half-line radial logarithmic Riesz expression have NOT yet been identified by a strict physical radialization theorem. Nor have source-time and moving-observer derivatives been combined for one dynamically varying 3D density; the moving Kummer fundamental pair, all four-piece PDE residual gain O(s^(-9/4)), direct threshold Lipschitz, and final dynamically derived Type-II exponent remain OPEN. No artificial radius law or rate was postulated. Formal revised-manuscript environment tally is **11/13 (84.62%)**; auxiliary successes do not increment the numerator.


## 2026-11-08 original Hartree critical scaling removes the moving-observer time derivative (strict)

The remaining original-source term was NOT replaced by arbitrary forcing. The exact energy-critical covariance of the ORIGINAL inverse-square quartic mixed interaction, **including all three radial logarithmic Riesz terms**, is formally established:

`ActualHartreeCriticalScaledInteraction.lean`, strict [CI 42478335181](https://github.com/penghongzhong/HBL/actions/runs/42478335181) **SUCCESS**, source revision 556ed982. For V_a(r)=sqrt(a)V(ar), Z_a(r)=sqrt(a)Z(ar), `I(V_a,Z_a)(r)=a^2 sqrt(a) I(V,Z)(ar)`, in particular `sqrt(a) S_K(r)=I(V_a,Z_a)(r)` with **exact original unsigned source** `S_K(r)=a^2 I(V,Z)(ar)` and actual Green forcing `F0(r)=-S_K(r)`. No remainder, auxiliary local forcing, or prescribed Type-II rate.

`ActualHartreeTrueMovingOriginalSourceFromScaledOrbit.lean`, corrected revision 7b5a37e, strict [CI 42478989692](https://github.com/penghongzhong/HBL/actions/runs/42478989692) **SUCCESS**. Differentiates the same original **unsigned** moving-observer Kummer source by differentiating its fixed-normalized-observer true rescaled interaction and the actual sqrt(a) prefactor. **HasDerivAt(S_K)** is NOT a hypothesis; the actual negative forcing derivative follows by negation.

`ActualHartreeTrueSourceTimeFromPhysicalScaledOrbit.lean`, corrected revision 0284837a, strict [CI 42479363866](https://github.com/penghongzhong/HBL/actions/runs/42479363866) **SUCCESS**. This is the FULL direct composition with `ActualHartreeFullInteractionTimeFromOrbit`: the derivative of the original unsigned moving Kummer Hartree source is derived from primitive pointwise C1 of the actual twice-rescaled real monopole/complex radiation and original quartic-velocity logarithmic Riesz integrable majorants. Neither the original moving source derivative NOR ANY of the three original Hartree potential derivatives is assumed. The source carries no prescribed blow-up exponent.

`ActualHartreeTwoStageCoreTimeTangent.lean`, corrected revision 92f6af9, strict [CI 42479257326](https://github.com/penghongzhong/HBL/actions/runs/42479257326) **SUCCESS**: the actual double scaled monopole V_{a,c}=sqrt(a)V_c(ar) has its time tangent derived from a_s,c_s and the genuine cutoff cancellation THROUGH c=0. This removes the independent real core time-derivative input for that field given physical a,c differentiability.

`ActualHartreeTwoStageRadiationTimeTangent.lean`, corrected revision 49761a1, independently derives the other input from one original two-variable C1 complex radiation and the actual a_s,ell_s. Dedicated [CI 42479553379](https://github.com/penghongzhong/HBL/actions/runs/42479553379): **STRICT SUCCESS**.

The related mathematics and notation are synchronized to `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`, latest synchronized TeX commit 1e5cc51, with the unsigned-source/negative-forcing sign explicitly distinguished. The new critical-scaling route ELIMINATES the need to differentiate the logarithmic radial observer argument a(s)r directly: all source time dependence is moved to a genuine nonlocal interaction at a FIXED normalized Kummer radius. This is a genuine shorter proof route; the separate original 3D noncompact spatial observer proof is not misidentified with the radialized kernel.

**Noncircularity:** These successful CONDITIONAL mathematical theorems retain actual C1 of original high-regularity physical radiation and original quartic Riesz velocity domination as input; no genuine Hartree PDE existence/trapping or global matching is derived from these. Remaining: physical Z time/spatial regularity on one orbit; time-varying Kummer basis, all-domain complete four-piece nonlocal PDE residual `O(s^(-9/4))` with relative gain, threshold Lipschitz, real finite recursion and finally the dynamically selected Type-II rate. **The revised manuscript environment count remains 11/13 (84.62%).**


## 2026-11-08 strict original source-norm elimination in one spectral Green step

**STRICT SUCCESS** [CI 42485891640](https://github.com/penghongzhong/HBL/actions/runs/42485891640), source commit `2ab28476aa304be6c727282c0fdf9b056a778777`,
`HBL/TypeIIDynamicSelection/ActualHartreeOriginalSelectedSpectralSourceNormGain.lean`.

The exact proof begins with the genuine full quartic nonlocal Hartree Riesz source, actual original H+/H- Fredholm weighted data, and the original source-derived unique real compatibility speed (NOT a free chosen p or a synthetic forcing). The existing physical corrected-envelope producer constructs Qa>=0 and
`||Fadj(r)|| <= Qa/r²`, `Qa<=Csel*(N_F+Cphys*ell^(1/8))`.
The original Wronskian Green inversion then constructs the first spectral correction u1=G_K0[(b(mu,theta)-b(mu0,theta0))*G_K0[Fadj]], and verifies EXACT
`L_{mu,theta}(u0-u1)-Fadj=-delta*u1`
with a quadratic error bound using **only** these initial physical norms. Crucially, the former **independent** bound `||Fadj||<=M` is completely eliminated.

Exact target audit: strict `--trust=0`, warning-as-error, target `#check` and target `#print axioms` succeed. The retrieved build artifact 13618619099 has EMPTY strict.log, source SHA256 evidence, compiler version Lean 4.35.0-rc3, and EXACT axioms `[propext, Classical.choice, Quot.sound]` with no `sorryAx`. This is one successful auxiliary theorem, **not** a full revised manuscript environment.

**Mathematical limitation:** The resulting bound has factor
`(abs(mu-mu0)+abs(theta-theta0))² * [2*Ck³*(B-r0)]² / r0²`
with `r0=L/a`. This is NOT independently known to be time-small. Neither delta/r0 nor a uniform moving-left-endpoint original Kummer basis constant has yet been shown to have a positive time order from the same PDE orbit. The first Green correction also changes boundary traces and must be tied to the physical Fredholm/repair/remote field in all three regions. The full nonlinear 3D Hartree residual `O(s^(-9/4))`, its direct threshold Lipschitz, actual finite recursion and derived Type-II rate remain open.

Mathematics synchronized in `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`, commit `b83f5b96cebca4f9872a42caf7848e88f6ec04c3`. Formal revised count **11/13 = 84.62%**; do NOT count this local spectral estimate as 12/13.


## 2026-11-08 exact physical Wronskian cancellation — three strict successes

The last source-norm elimination theorem had a crude `r0^-2` factor from prematurely replacing `||Fadj(r)|| <= Qa/r^2` by the constant `Qa/r0^2`. This factor is **now eliminated at its mathematical origin** using the exact original normalized Kummer Wronskian identity `||W_K(r)^(-1)||=r^2`.

**New source-faithful strict proof chain:**

1. [CI 42486794147](https://github.com/penghongzhong/HBL/actions/runs/42486794147), corrected source commit `e502dc56974b368426533769ebb95fa0a3fa76a7`, `HBL/KummerOriginGreen/InverseSquareSourceNoLeftRadiusLoss.lean`. For `||F(r)||<=Qa/r²`, derive BOTH original Green source density bounds `<=Ck*Qa`, BOTH Wronskian coefficient integral bounds and `||G_K[F](r)||+||∂_rG_K[F](r)|| <= 2*Ck²*(B-r0)*Qa`. No explicit `r0^-2`.
2. [CI 42486794135](https://github.com/penghongzhong/HBL/actions/runs/42486794135), source commit `ef7484c2b6227263364fa5afda9992e99536565e`, `ActualHartreeFixedKummerSpectralNoLeftRadiusLoss.lean`: the ACTUAL first spectral Green correction `u1=G_K0[delta*G_K0[F]]` satisfies exact `L_{mu,theta}(u0-u1)-F=-delta*u1`; the residual bound is `||delta||²*(2*Ck²*(B-r0))*(2*Ck³*(B-r0))*Qa`.
3. [CI 42486875347](https://github.com/penghongzhong/HBL/actions/runs/42486875347), source commit `858bec646e725a26363de4e9a71f22f5bdbbc66c`, `ActualHartreeOriginalSelectedSpectralNoRadiusLoss.lean`: instantiates BOTH Green fields using the SAME genuine quartic inverse-square Hartree source and its uniquely compatible real two-channel Cramer selection. The physical corrected outer norm `Qa<=Csel*(N_F+Cphys*ell^(1/8))` is derived from the original Fredholm and radiation inputs, not taken as a new hypothesis. **No independent M, Qa, or modulation pair is assumed.** Therefore the source-specific quadratic bound has **no explicit inverse matching radius factor**.

**Independently extracted and audited all three GitHub Actions evidence archives:** 13619188816, 13619548762, 13619213733. Each archived `strict.log` is empty; each exact-target `#print axioms` reports precisely `[propext, Classical.choice, Quot.sound]`; fixed Lean 4.35.0-rc3, pinned Mathlib `a98628e16`, trust-zero and warning-as-error. No `sorryAx`, no new axiom.

**Important remaining physical proof obligations:**
- The annular physical basis constant `Ck` in `OriginBasisOn K r0 B Ck` may itself depend on the moving left interface `r0`. The explicit `r0^-2` cancellation does **NOT** establish a uniform basis norm as `r0 -> 0`.
- The actual spectral parameter displacement `delta(t)` still requires a PDE-derived positive time order, and the second Green correction modifies real lower/upper physical interface traces. A new matched repair must preserve full three-junction `C^1` compatibility.
- The full original three-dimensional Hartree nonlinear interaction, its real four-piece time/space derivatives, remote Riesz feedback, uniform `O(s^-9/4)` residual, direct threshold Lipschitz and genuine finite recursion are **not** consequences of this single Kummer spectral cancellation.
- The Type-II blowup law must be DERIVED from the eventual actual PDE orbit, never inserted as an exponent assumption.

Manuscript formulas synchronized in `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`, commit `1748b40ea75dadca7e016002c1b045134867d8fb`. Revised original environment count **11/13 = 84.62%**; §2.13 and the final dynamically selected Type-II theorem are STILL OPEN.


## 2026-11-08/09 strict extension: original spectral PDE defect AND C¹ trace on one annulus

- New verified theorem module: `HBL/TypeIIDynamicSelection/ActualHartreeOriginalSpectralC1TraceNoRadiusLoss.lean` at commit `dc810e60f79e8857870450daf82fd29e6e5da736`.
- Strict CI: https://github.com/penghongzhong/HBL/actions/runs/42500440029 — **SUCCESS**.
- Source-faithful inputs: original `OriginKummerPair`, `OriginBasisOn K a b C`, `0<a≤b`, and actual inverse-square forcing bound `‖F(r)‖≤Q/r²`; the selected genuine Hartree source from the prior CI `42486875347` supplies this forcing envelope.
- New two-coordinate jet theorem:
  ```
  ||(G0[F]-G0[dG0[F]])(r)-G0[F](r)||
  + ||(S0[F]-S0[dG0[F]])(r)-S0[F](r)||
     <= [2 C³ (b-a)] |d| [2 C² (b-a)] Q.
  ```
  In the SAME theorem, the exact original radial Kummer PDE residual is at most
  `|d|² [2 C² (b-a)] [2 C³ (b-a)] Q`.
- Independently downloaded the CI archive `13626205016`: `strict.log` is empty, compiler is Lean 4.35.0-rc3, and exact `#print axioms` for both theorem declarations is `[propext, Classical.choice, Quot.sound]`, without `sorryAx`.
- Human-readable matching mathematics synchronized in `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`, commit `b30c5ebedbc15fe464366833316f3630e00e4a5d`.
- The new theorem controls the change in Cauchy data, but does **not** preserve the left Fredholm jet or cancel the new upper outgoing obstruction. The left-preserving full matched spectral correction and radius-uniform regularized Wronskian/Volterra tools are under new dedicated CIs. Their success is NOT assumed here.
- Formal revised original environment count is still **11/13**. `§2.13` requires a uniform genuine full-PDE remainder gain; the dynamically derived Type-II theorem is also OPEN.
