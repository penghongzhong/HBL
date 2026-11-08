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
