# HBL §2.13 shortest strict proof chain (8 November 2026)

**Formal original-paper acceptance: 11/13.** Original revised §2.13 is not
accepted; the final Type-II blowup theorem is not accepted. Do **not** promote
counts on the basis of auxiliary theorem numbers or passing independent CI
jobs. Pin Lean **4.35.0-rc3** and Mathlib
**a98628e16c11f5167f16124105ddce53efa9bfe5**.

## Mathematically substantive strict successes

| Node | Real mathematical statement | Strict GitHub CI |
|---|---|---|
| H0 | Physical three-dimensional Hartree Riesz source supplies its genuine annular inverse-square envelope and a unique real compatible two-speed selector, without treating a speed bound as external data. | Established preceding source-selection modules; see `ActualHartreeTrueSourceSpeedSelection.lean`. |
| H1 | Original Hartree selected source yields a first-order fixed-basis spectral C¹ jet perturbation and quadratic frozen-Kummer PDE residual; **no explicit** left-radius inverse-power prefactor. | [42500440029](https://github.com/penghongzhong/HBL/actions/runs/42500440029), **Success**, `ActualHartreeOriginalSpectralC1TraceNoRadiusLoss.lean`. |
| H2 | Complete Cramer-matched spectral correction preserves both left Fredholm Cauchy coordinates exactly and identifies the **nonzero, generally** upper outgoing defect exactly. | [42502178507](https://github.com/penghongzhong/HBL/actions/runs/42502178507), **Success**, `ActualHartreeMatchedSpectralLeftC1Exact.lean`. |
| H3 | Original Wronskian inverse-linear Green density bound using bounded regularized Kummer IVP modes, no (r_0^{-1}) factor. | [42502314380](https://github.com/penghongzhong/HBL/actions/runs/42502314380), **Success**, `InverseLinearSourceRegularizedNoRadiusLoss.lean`. |
| H4 | Complete Cramer zero-left-jet formula and uniform weighted Volterra bound (\lVert rG[q,0,0](r)\rVert\le 2G^2(B-r_0)M). | [42503893981](https://github.com/penghongzhong/HBL/actions/runs/42503893981), **Success**, `ActualHartreeZeroLeftRegularizedVolterra.lean`. |
| H5 | Original outgoing compatibility mismatch bounded by regular mode alone, (\lVert \mathcal T_B[v]\rVert\le G|\delta|H(B-r_0)), conditional on the actual matched profile weighted field estimate. | [42503498370](https://github.com/penghongzhong/HBL/actions/runs/42503498370), **Success**, `ActualHartreeMatchedSpectralUpperFluxWeighted.lean`. |

Verified retained evidence archives for H1, H2, H4, and H5 contain exact
`#check` theorem types and `#print axioms` dependencies. Each listed
audited theorem depends only on Lean's `propext`, `Classical.choice`
and `Quot.sound` (possibly printed with universe annotations), with no
`sorryAx`. The strict workflow requires `--trust=0`,
`-DwarningAsError=true`; the above statuses are real GitHub Actions
conclusions, not local assertions.

## Strictly accepted source-to-weighted-correction integration

- `ActualHartreeOriginalSelectedSpectralC1Joint.lean` combines the
  **same real selected physical Hartree source** with the joint source-driven
  first-order C¹ and second-order Kummer residual bound.
  Strict workflow: [42504110208](https://github.com/penghongzhong/HBL/actions/runs/42504110208), **Success**.
- `ActualHartreeMatchedSpectralRegularizedQuadratic.lean` converts the
  actual matched profile's **weighted** bound to a genuinely zero-left-jet
  correction with quadratic spectral defect; this step **alone** does not
  produce the weighted bound from a physical orbit.
  Strict workflow: [42504361153](https://github.com/penghongzhong/HBL/actions/runs/42504361153), **Success**.
- `ActualHartreeMatchedOriginalSourceWeightedSpectral.lean` derives
  **rather than assumes** the weighted first Cramer-matched profile from the
  original inverse-square source and actual Fredholm left Cauchy jet, then
  passes it into the zero-left regularized spectral gain.
  Strict workflow: [42504578042](https://github.com/penghongzhong/HBL/actions/runs/42504578042), **Success**.

The three preceding workflows are now **strictly successful** (independent
Lean compilation, exact theorem type, original pinned kernel and axiom audit).
Their conclusions are limited to their literal fixed-annulus theorem types;
none establishes revised original §2.13.

## New regular Cramer-jet proof chain: CI not yet accepted

- `ActualHartreeMatchedRegularJetNoRadiusLoss.lean`: original Wronskian
  cancellation in the **actual regular Cramer coefficient**
  \(|\gamma_{\rm reg}|\le
  G\{r_0\|DU\|+(r_0+1)\|U\|\}\), plus the \(r\)-weighted regular mode
  bound independent of any \(r_0^{-1}\) or unweighted singular Kummer basis.
  [42505966960](https://github.com/penghongzhong/HBL/actions/runs/42505966960),
  **unaccepted until strictly successful**.
- `ActualHartreeMatchedSourceUniformRegularJet.lean`: combines the
  **same original inverse-square source** and compatible Fredholm left jet
  with the regular-coefficient cancellation to bound the complete weighted
  first matched field and the second-order spectral defect. The remaining
  Green contribution still contains the original `OriginBasisOn`
  constant. Latest [42506363468](https://github.com/penghongzhong/HBL/actions/runs/42506363468),
  **unaccepted until strictly successful**.
- `ActualHartreeTrueSelectedMatchedFirstWeighted.lean`: substitutes the
  **unique real selected speed** from the genuine Hartree source, the
  actual corrected inner Fredholm jet and its generated outer \(Q_a\) into
  that matched profile estimate. It has no independently assumed jet
  or adjusted source bound; the true *time-dependent* orbit is not yet
  constructed. [42506528872](https://github.com/penghongzhong/HBL/actions/runs/42506528872),
  **unaccepted until strictly successful**.

**Pending is not Success.** Inspect any failed decoded strict job log and
repair Lean before accepting any of these three new statements. An earlier run, [42501019413](https://github.com/penghongzhong/HBL/actions/runs/42501019413),
failed on definitional derivative/continuity rewrites and was repaired in
successful successor H2. [42501379178](https://github.com/penghongzhong/HBL/actions/runs/42501379178)
failed because of that upstream dependency; successful successor H5
resolves the actual upper-flux branch.

## Remaining load-bearing nodes (not accepted)

```text
TRUE PHYSICAL ORBIT
  [✓] Genuine nonlocal Hartree source + unique real two-speed selector
    [✓] Source-driven fixed frozen-Kummer quadratic residual
    [✓] Exact left C1-preserving matched correction
    [✓] Regularized outgoing flux and zero-left weighted Volterra mapping
    [?] Derive uniform moving-radius first-profile bounds for SAME orbit (new regular-jet cancellation in strict CI)
    [?] Select continuously differentiable modulation path; moving Kummer basis
    [?] Remove spectral correction outgoing obstruction with SAME two speeds
    [?] Actual globally matched THREE C1 joins after spectral correction
    [?] Full FOUR REGION nonlocal PDE error of positive time order
    [?] Genuine finite iteration preserving all controls
  [X] Revised original §2.13 complete strict theorem → 12/13
  [X] Derive actual II-type finite-time blowup rate from physical PDE
  [X] Final original main theorem complete strict proof → 13/13
```

Do not treat `OriginBasisOn K r_0 B C` with a fixed `C` as a
uniform moving-left-radius estimate, or use a prescribed decay for
`\delta(t)` or the blowup exponent. Only the actual four-region
nonlinear PDE recurrence can close the original paper's load-bearing
unproved steps.

Manuscript §2.13 source:
`verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`.


## November 8 strict Cramer-jet repair, synchronized with §2.13

- Re-read the decoded strict job logs for [42508165467](https://github.com/penghongzhong/HBL/actions/runs/42508165467) and [42508165489](https://github.com/penghongzhong/HBL/actions/runs/42508165489): both **FAILED** on the *same* upstream Lean type mismatch at `ActualHartreeMatchedRegularJetNoRadiusLoss.lean:133`, not on the physical PDE estimate.
- The `mul_le_mul` application incorrectly supplied `0 ≤ G` where the actual required premise was
  `0 ≤ G * (a * ‖DU‖ + (a + 1) * ‖U‖)`. The full premise follows from `a>0`, `G≥0`, and nonnegativity of the two original Cramer-jet norms. The repair keeps the literal physical coefficient estimate and no source assumption is modified.
- Source repair commit [2d94b7ce](https://github.com/penghongzhong/HBL/commit/2d94b7ce7d72388aacfb8e817069b45834ce936a); manuscript clarification commit [8b6e09ea](https://github.com/penghongzhong/HBL/commit/8b6e09eac8589a8e799f3908e78c0064d3cb93f4).
- Exact replacement strict CI: [42511347313](https://github.com/penghongzhong/HBL/actions/runs/42511347313) (Cramer coefficient and weighted regular mode), [42511347298](https://github.com/penghongzhong/HBL/actions/runs/42511347298) (source to weighted matched profile and spectral correction), [42511347279](https://github.com/penghongzhong/HBL/actions/runs/42511347279) (same true Hartree source to unique real speed and physical Fredholm left jet). At this checkpoint these were **IN PROGRESS**, not yet accepted; inspect their final conclusions, strict logs, exact `#check` types and individual `#print axioms` before marking any strict success.
- Independently inspected the artifact of [42500440029](https://github.com/penghongzhong/HBL/actions/runs/42500440029): empty `strict.log`, pinned compiler and the two precise theorem reports contain only `propext`, `Classical.choice` and `Quot.sound` (universe-level annotations do not add axioms).
- The outstanding *mathematical* obstruction has NOT been dismissed: `OriginBasisOn K (L/a) B C` is a fixed-annulus budget with potentially singular physical basis; no uniform moving-radius estimate, four-region nonlinear positive-time residual or actual finite packet recursion follows from this pointwise Cramer regular-mode improvement.

**Formal acceptance unchanged: 11/13**. Original revised §2.13 and the final dynamical Type-II theorem remain unproved and are not replaced by conditional auxiliary estimates.


### Accepted Cramer regular-jet proof, source-dependent composite still rechecking

**STRICT SUCCESS:** [42511347313](https://github.com/penghongzhong/HBL/actions/runs/42511347313), pinned source SHA `2d94b7ce7d72388aacfb8e817069b45834ce936a`. Downloaded and inspected the published artifact: zero-byte `strict.log`, exact Lean 4.35.0-rc3, exact `#check` types of both
`actual_Hartree_matched_regular_coefficient_no_left_radius_loss` and
`actual_Hartree_matched_regular_part_weighted_no_radius_loss`;
both `#print axioms` reports list only `propext`, `Classical.choice`, `Quot.sound` (including universe annotations). The theorem directly cancels the moving left-radius inverse Wronskian loss for the actual regular homogeneous component.

**Not yet accepted:** upstream-cleared true selected-weighted composite [42511347279](https://github.com/penghongzhong/HBL/actions/runs/42511347279) failed at `ActualHartreeTrueSelectedMatchedFirstWeighted.lean:157:4` solely from a no-progress `dsimp only`. Deleted that redundant tactic in commit [23171a5a](https://github.com/penghongzhong/HBL/commit/23171a5a0521ddf4d0c17bf028ebfc74d79d4311); replacement [42512365232](https://github.com/penghongzhong/HBL/actions/runs/42512365232) is **IN PROGRESS** at this checkpoint. The other source-to-spectral composite [42511347298](https://github.com/penghongzhong/HBL/actions/runs/42511347298) is also **IN PROGRESS**. Neither is accepted until strict audit passes.

Manuscript `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex` now cites this verified regular-coefficient bound, but the global source-to-spectral composite and all time-dependent full-Hartree residual claims keep their own strict status. The formal original environment count is **11/13**.


### Strict acceptance of the source-derived complete matched spectral subchain

**STRICT SUCCESS:** [42511347298](https://github.com/penghongzhong/HBL/actions/runs/42511347298), same pinned source commit `2d94b7ce7d72388aacfb8e817069b45834ce936a`. Fetched the archived artifact and checked its `strict.log` (empty), compiler version (Lean 4.35.0-rc3), exact `#check` and `#print axioms` for all three declarations:
`actual_Hartree_matched_source_and_uniform_regular_jet_weighted`,
`actual_Hartree_matched_source_regular_jet_quadratic_spectral_error`,
`actual_Hartree_matched_source_regular_jet_spectral_outgoing_bound`.
Each depends exactly on `propext`, `Classical.choice`, `Quot.sound` with no `sorryAx`. This closes the **same fixed-annulus inverse-square source + actual Fredholm Cramer left jet → derived weighted matched first profile → genuinely quadratic frozen spectral error and explicit nonzero outgoing mismatch** subchain. The full physical unique-speed specialization on the same source needs its own replacement CI [42512365232](https://github.com/penghongzhong/HBL/actions/runs/42512365232).

No claim of a moving-Kummer uniform `OriginBasisOn` constant, full four-region PDE order gain, physical packet induction or inferred blowup rate is licensed by this subchain; formal count remains **11/13**.


### Next indispensable mathematical simplification: remove the hidden shrinking-annulus basis loss

A **literal audit** of the existing derived certificate
`origin_kummer_annulus_bound` in `HBL/KummerOriginBasis/AnnulusBound.lean` shows
`OriginBasisOn K r0 B (G*(1/r0+1/r0^2)+B^2+1)` for `r0>0`.
Thus a bound that has **no explicitly written** `r0^{-2}` is not automatically uniform when its `Ck` is such a certificate. Do not feed this exploding `Ck` into the full spectral correction and call it a time gain. This is a genuine issue with the coarse physical singular basis, not a Lean tactic bug.

Use the **same physical source-selected** decomposition
`Fo=F0-p_b S_b-p_omega S_omega` and the exact matched field
`w(r)=Y(r) A_Fo(r)+X(r) B_Fo(r)+gamma_reg X(r)`,
where `Y=y/r`, `X=x/r` and the compatible singular homogeneous coefficient is zero. Replace the coarse `OriginBasisOn` norm on the *complete* source field with three independently already derived **physical components**:
(i) `ActualHartreeTrueSourceSelectedFullSingularOriginalNorm.lean` controls the **whole singular product** `Y A_Fo` directly by original `N_F+Q_H` without the shrinking-scale loss;
(ii) `ActualHartreeRegularOriginCoefficientSourceBound.lean` and the newly accepted Cramer weighted estimate control the exact `gamma_reg X` from the original corrected Fredholm jet and source;
(iii) the remaining **regular Green product** `X B_Fo` must be bounded at **all intermediate radii**, not just at `B`, by combining the genuine baseline Hartree Riesz coefficient estimate and `ActualHartreeSpeedRegularGreen.lean`'s true `O(a B)` speed-source density bound (with the unique selected speeds). A blanket `Q_H/r^2` substitution for the speed channels is too weak and introduces a spurious logarithm; preserve their genuine `O(a/r)` decay.

Only after proving (iii) for the SAME selected source can one substitute a truly uniform, explicitly source-derived weighted first-profile bound in the audited zero-left spectral quadratic Volterra estimate. Then prove the matching `C^1` outgoing repair and the **full same-orbit four-region Hartree time-order gain**, before real physical packet recursion. This is a proposed analytical reduction, **not** an accepted new theorem or assumed estimate; original count stays **11/13**.

### November 8 continuation — source-derivable exact Green-moment spectral step

Confirmed the selected source–unique real speed–actual corrected Fredholm left jet proof is now **strict Success**:
[42512365232](https://github.com/penghongzhong/HBL/actions/runs/42512365232),
source SHA `23171a5a0521ddf4d0c17bf028ebfc74d79d4311`. Its workflow
executes `lake env lean --trust=0 -DwarningAsError=true`, the exact
`#check @actual_Hartree_true_source_unique_speed_matched_weighted_from_Fredholm_jet`,
and a one-declaration `#print axioms` audit with allowable
`propext`, `Classical.choice`, `Quot.sound` and no `sorryAx`.
Do not confuse this fixed-annulus theorem with an actual moving-time
uniform full PDE estimate.

**New substantive Lean step:** `ActualHartreeExactGreenMomentsMovingSpectral.lean`
(commit [96562fe1](https://github.com/penghongzhong/HBL/commit/96562fe1bcbf855612bee1c449f4ca68da237376))
makes the mathematical cancellation `r*(Y A+X B)=y A+x B` *before*
taking norms; it bounds the exact original Green response and the
fixed-basis varying-spectral defect solely by **both literal Green
source integrals**, a global regularized-mode constant `G`, and the
actual spectral-parameter difference, without any assumed `OriginBasisOn`
constant and its hidden `r0^{-2}` loss. The third statement instantiates
the original time-dependent adjusted nonlocal Hartree source verbatim.

Pinned 3-type/3-axiom strict workflow
`.github/workflows/hbl-213-exact-green-moments-spectral.yml`
was first rejected by GitHub for a malformed duplicate trailing block;
fixed in commit
[097174eb](https://github.com/penghongzhong/HBL/commit/097174ebb37a18754f6d5abfbe5a208e10a3a6d1).
Its replacement [CI 42518163620](https://github.com/penghongzhong/HBL/actions/runs/42518163620)
is **IN PROGRESS** at this checkpoint, *not accepted*.

The same formula is synchronised into
`verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`
(commit [c6b4da4d](https://github.com/penghongzhong/HBL/commit/c6b4da4df7b1bc4fc07257ef418e7938b6b38eca)).
This fixes **only the algebraic exposure of the hidden constant**;
it does not derive bounds for the remaining actual regular moment
`B_Fo` under unique real speed, prove three C¹ joins of the *spectrally
corrected* whole field, derive four-region source-norm relative time gain
or perform the physical finite PDE recursion. The original §2.13 remains
OPEN, **11/13**. No preassigned II-type rate or time-decay hypothesis.

### Next source-faithful ingredient — BOTH regular speed Green moments at ALL radii

The pre-existing `ActualHartreeSpeedRegularGreen.lean` theorem bounds each
real-speed lower-origin Green moment `CoeffB` at **any permitted endpoint**:
`‖CoeffB_(P_j)(B)‖ ≤ C_sp G a B`.
New module `HBL/TypeIIDynamicSelection/ActualHartreeSpeedRegularGreenAllRadii.lean`,
commit [c6064492](https://github.com/penghongzhong/HBL/commit/c6064492a17cc9d8a972374bfbf99fd3bc956b27),
uses precisely **that theorem with upper endpoint B:=r** for every
`r ∈ Icc (L/a) B`. The same constant works, since `r≤B≤1` and
`r<scale`; monotonicity proves
`∀r, ‖CoeffB_(P_scale)(r)‖, ‖CoeffB_(P_phase)(r)‖ ≤ C_sp G a B`,
with no independent source bound and no spurious logarithm.
New strict exact type / standard axiom workflow:
[CI 42518450478](https://github.com/penghongzhong/HBL/actions/runs/42518450478)
is **in progress**, not accepted at the checkpoint.
The statement is synchronized in §2.13 TeX commit
[654f7e1b](https://github.com/penghongzhong/HBL/commit/654f7e1bacc0eb28c9e1787074034d53ec3681a6).

For the same selected p, the resulting selected speed contribution
has the mathematically derived form
`a(|p.1|+|p.2|) C_sp G B ≲ (N_F+Q_H)`, using the strict real Cramer
bound `|p.1|+|p.2| ≤ C_sel (N_F+Q_H)/a`. A final theorem must apply
the true original source `F0` to obtain the `CoeffB(F0)` part,
then formalize Green integral linearity at **every** r and join all
three physical terms to the exact weighted spectral formula.
Do not count either candidate module or this argument as revised 2.13.

Formal revised original environment count **11/13**.

### Original Riesz source to WHOLE weighted Green field — candidate direct composite

Located **strict accepted [42441060509](https://github.com/penghongzhong/HBL/actions/runs/42441060509)** in
`ActualHartreeKummerRegularTailGain.lean`; its theorem
`actual_Hartree_scaled_Kummer_both_Green_coefficients_uniform`
already controls **both** original upper and lower Green coefficients
at every physical radius for the same literal full Riesz source
`F0=-actualHartreeLaplacianScaledKummerSource a ell c z`:
`‖CoeffA(F0)(r)‖, ‖CoeffB(F0)(r)‖ ≤ (8/3) G Q_H L^(-3/8)`.
This solves the unadjusted-source part of the two-moment problem
directly without reconstructing rpow integration. No implied new
source-envelope premise is needed.

Composite file `HBL/TypeIIDynamicSelection/ActualHartreeOriginalFullGreenWeightedGain.lean`
commit [92ae187c](https://github.com/penghongzhong/HBL/commit/92ae187cc528940a69c5666be22daa7e84acabba)
connects that genuine two-coefficient source theorem to the new exact
radius-weighted Green identity, producing the complete original field bound
`‖r*Green(F0)(r)‖ ≤ (16/3) G^2 Q_H L^(-3/8)` at every r, with no
hidden `OriginBasisOn` constant. Its dedicated pinned exact type/axiom
[CI 42518707587](https://github.com/penghongzhong/HBL/actions/runs/42518707587)
is **IN PROGRESS**, so the new composite is not yet accepted. The
corresponding mathematical proof has been added to the §2.13 manuscript,
commit [71071699](https://github.com/penghongzhong/HBL/commit/71071699983d28a73e926d492c63a2587d0a24c5).

**Next shortest link:** combine (1) this true full baseline field
`Green(F0)`, (2) the source-faithful uniquely selected
`(p_1,p_2)` from CI 42512365232 and (3) the two speed
regular Green-moment all-radii bounds under CI 42518450478,
together with the already strictly accepted outgoing singular-speed
product, to derive a genuinely *source-only uniform* weighted
`Green(F0 - p_1 P_sc - p_2 P_ph)` estimate.
Then use the exact Cramer Fredholm regular jet and spectral correction
without `Ck(r0)`, repair each of three physical C¹ boundaries, and
derive positive time gain from the actual full nonlocal Hartree PDE
rather than from an a priori budget. No increase from **11/13**.

### Nov 8 additional genuine unique-selector bridge and first CI repair

New `ActualHartreeTwoSpeedRegularGreenAllRadii.lean`, commit
[9473840d](https://github.com/penghongzhong/HBL/commit/9473840d4fdc889e9038b37a55ca4e17d89f920a),
formalizes original Wronskian **integral linearity** with exact
interval-integrability certificates for the two genuine real-speed
directions. It derives for all r:
`‖CoeffB(-p1 P_scale-p2 P_phase)(r)‖ ≤ C_sp G a B (|p1|+|p2|)`,
not a freely assumed adjusted source envelope. Its strict pinned
[CI 42518956191](https://github.com/penghongzhong/HBL/actions/runs/42518956191)
is in progress.

New `ActualHartreeSelectedSpeedRegularGreenAllRadii.lean`, commit
[24e9b80d](https://github.com/penghongzhong/HBL/commit/24e9b80d9fd4910174e8777b6c5c1c9015b9242c),
composes the literal physical three-dimensional quartic Hartree source
unique real two-speed Cramer producer with this genuine all-radii
regular-moment estimate, using the SAME p; it removes a from
`(C_sp G a B) * (C_sel/a) (N+Q)` to conclude
`‖CoeffB(F_sp)(r)‖ ≤ C_sp G B C_sel (N+Q)`
without supplied bound on selected velocity.
Dedicated pinned [CI 42519156651](https://github.com/penghongzhong/HBL/actions/runs/42519156651)
is in progress. Both mathematical formulas are synchronized in
§2.13 TeX commit
[b467ffe3](https://github.com/penghongzhong/HBL/commit/b467ffe3689d6f119766a5f01a24cadfbf4ac1a4).

First run of exact original Green spectral moment
[CI 42518163620](https://github.com/penghongzhong/HBL/actions/runs/42518163620)
**FAILED** on a genuine warning-as-error:
Lean compiler `ActualHartreeExactGreenMomentsMovingSpectral.lean:35:30`
reported unused binder `hab`; original CI log was actually downloaded.
The mathematical proof had no reported failed goals. Changed
`(hab : a ≤ B)` to `(_hab : a ≤ B)`, with same exact type and
logical strength, commit
[9c528cbd](https://github.com/penghongzhong/HBL/commit/9c528cbda7d5c99c7b41b34e52863f2a01c98755).
Replacement pinned [CI 42519218237](https://github.com/penghongzhong/HBL/actions/runs/42519218237)
is in progress. No premature CI success is declared.

The original formal environment counter remains **11/13**; the
complete revised original §2.13 and full Type-II blowup rate from
the original PDE have not been proved.


### November 8, 2026, new strict original-Green acceptance and no-loss chain

- **Strict Success [42522024695](https://github.com/penghongzhong/HBL/actions/runs/42522024695)**, pinned source [38468393](https://github.com/penghongzhong/HBL/commit/38468393d9a8a68a5a9874780ee654b0415aaebe): `actual_Hartree_speed_regular_Green_coefficients_all_radii`. Reuses the actual Wronskian source integrals with each intermediate radius as upper endpoint, avoiding both a spurious logarithm and a moving-left-radius inverse power.
- **Strict Success [42522041952](https://github.com/penghongzhong/HBL/actions/runs/42522041952)**, pinned source [f8c7223c](https://github.com/penghongzhong/HBL/commit/f8c7223c33c02dea94260c6fe6129aaf84a054ea): `actual_Hartree_true_source_selected_regular_Green_moment_all_radii`. This selects one unique real compatible speed from the original Hartree source, then cancels the physical scale `a` in the actual speed-generator regular Green moment.
- The former two-real-speed *standalone* CI **42522033344 failed** exclusively on Lean's strict “merge introductions” linter at line 57. Its source was repaired without changing the theorem type in [391e432c](https://github.com/penghongzhong/HBL/commit/391e432c47846f4f68d9828cf4542942ea29c0d3), and the replacement strict CI **42523167362** must be checked before standalone acceptance.
- New **independent strict candidates** submitted: `actual_Hartree_original_source_spectral_drift_weighted_no_radius_loss` (CI 42522171670), `actual_Hartree_adjusted_original_regular_Green_all_radii` (CI 42522403614), `actual_Hartree_true_source_selected_adjusted_regular_Green_all_radii` (CI 42522550180), and `actual_Hartree_true_source_selected_whole_original_Green_no_radius_loss` (CI 42523023871). Each uses the **literal original inverse-square quartic Hartree source** and exact normalized Wronskian integral. The last combines the singular + regular channels using the *same* unique real Cramer selector, not two independent selections. All are **unaccepted until verified Strict Success**. Corresponding manuscript proof calculations appear in `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`.
- These statements concern fixed-time original physical Green integrals and frozen spectral displacement. They do **not** claim a derived time decay for `mu(s)-mu0`, the true fully moving three-interface C¹ source field after spectral correction, the same-orbit nonlinear four-region PDE residual `O(s^(-9/4))`, the finite physical recursion, or the dynamically selected Type-II exponent.

**Formal revised retained manuscript count remains strictly 11/13.** Neither source-faithful all-radius Green control nor any number of auxiliary CI successes changes the original environment numerator.


### Independent retrieved CI evidence, exact Lean type and transitive axioms

The original GitHub Actions artifact ZIP files were downloaded and inspected, not inferred from workflow labels. Every listed artifact contains its original source hash, pinned Lean version, exact pretty-printed `#check @...` declaration, `#print axioms` report and **empty `strict.log`**:

| Strict CI | Evidence artifact ID | Target Lean declaration | Exact transitive axioms |
|---|---:|---|---|
| [42522024695](https://github.com/penghongzhong/HBL/actions/runs/42522024695) | 13634301842 | `actual_Hartree_speed_regular_Green_coefficients_all_radii` | `propext`, `Classical.choice`, `Quot.sound` |
| [42522041952](https://github.com/penghongzhong/HBL/actions/runs/42522041952) | 13634470670 | `actual_Hartree_true_source_selected_regular_Green_moment_all_radii` | `propext`, `Classical.choice`, `Quot.sound` |
| [42522171670](https://github.com/penghongzhong/HBL/actions/runs/42522171670) | 13634650113 | `actual_Hartree_original_source_full_Green_weighted_no_radius_loss`, `actual_Hartree_original_source_spectral_drift_weighted_no_radius_loss` | `propext`, `Classical.choice`, `Quot.sound` for **each** |
| [42522403614](https://github.com/penghongzhong/HBL/actions/runs/42522403614) | 13633912583 | `actual_Hartree_adjusted_original_regular_Green_all_radii` | `propext`, `Classical.choice`, `Quot.sound` |

All four archives independently report **Lean 4.35.0-rc3**. CI workflow source pins Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, invokes `lake env lean --trust=0 -DwarningAsError=true` and rejects unexpected axioms or `sorryAx`. The local `source-hashes.txt` members match each archived targeted source. The extended Hartree spectral-drift theorem is genuinely new and uses the original physical source, but **does not** derive a positive time exponent for `mu(s)-mu0`.

The standalone two-speed integral-linearity module `ActualHartreeTwoSpeedRegularGreenAllRadii.lean` has not yet received replacement Strict Success at this checkpoint. Likewise the unique selected **full adjusted** regular Green and **full inhomogeneous** Green composite require their own successful CI. The original revised retained environment count remains **11/13**.


### November 9 local strict proof-chain audit — actual zero-left Cramer correction and weighted quadratic defect

The following are **independent CI successes**, with the original zipped GitHub Actions evidence downloaded, opened, and matched to the exact target declarations. Every `strict.log` is empty, the compiler prints Lean 4.35.0-rc3, the exact public declaration is exported by `#check`, and the `#print axioms` output is a subset of `{propext, Classical.choice, Quot.sound}`; no `sorryAx` or extra axiom occurs:

| Strict CI | Archived evidence ID | Precise mathematical scope |
|---|---:|---|
| [42527186005](https://github.com/penghongzhong/HBL/actions/runs/42527186005) | 13635837748 | `actual_Hartree_same_selected_speed_whole_Green_and_three_C1`: literal source-selected unique real speed, full original weighted Green and **uncorrected** three real physical C¹ joins |
| [42527710745](https://github.com/penghongzhong/HBL/actions/runs/42527710745) | 13635489425 | `actual_Hartree_matched_from_weighted_original_Green_and_Cramer`: exact compatibility eliminates singular homogeneous Cramer coefficient; source Green and true Fredholm left jet control full matched weighted profile |
| [42528138223](https://github.com/penghongzhong/HBL/actions/runs/42528138223) | 13636920518 | `actual_Hartree_true_source_selected_whole_original_Green_no_radius_loss`: one **actual quartic 3D Hartree source and one unique real two-speed selector** produce a complete inhomogeneous original weighted Green bound without inverse left-radius loss |
| [42528244780](https://github.com/penghongzhong/HBL/actions/runs/42528244780) | 13636299493 | `actual_Hartree_zero_left_Kummer_regularized_Volterra_identity`, `...Volterra_value_bound`: genuine Cramer zero-initial-jet solution, normalized origin IVP and exact Wronskian give `||r w1(r)|| <= 2 G² (B-r0) M` for inverse-linear forcing, no singular-mode bound |
| [42528244771](https://github.com/penghongzhong/HBL/actions/runs/42528244771) | 13635649153 | `actual_Hartree_matched_zero_left_spectral_weighted_response`: the same first matched weighted profile `||r u0||<=H` produces `||r Gleft[delta u0]||<=2 G²(B-r0)|delta|H` |
| [42528244857](https://github.com/penghongzhong/HBL/actions/runs/42528244857) | 13635953752 | `actual_Hartree_matched_spectral_left_C1_weighted_quadratic_residual`: exact ORIGINAL matched spectral field preserves both left Fredholm Cauchy coordinates and has weighted quadratic PDE defect `||r(L_delta(u0-u1)-F)||<=2G²(B-r0)|delta|²H` |

The last two are genuine **intermediate** theorems using the first matched profile weighted norm `H`, NOT permission to insert an independent weighted envelope as the physical theorem's premise. The actual original Hartree source plus Cramer producer (`ActualHartreeTrueSourceSelectedWholeMatchedWeighted.lean`) aims to derive `H`; a separate composition (`ActualHartreeTrueSelectedMatchedSpectralQuadratic.lean`) removes the independent `H` premise, under original source continuity for classical differentiation. The right corrected repair and full spectral four-piece three-C¹ joins also have dedicated pending CIs. Their physical outputs must use the same selected speed and the actual newly corrected upper jet.

**Latest strict-replay candidates at time of this audit:** CI 42528957269 (genuine source-selected entire Cramer weighted field), CI 42528956845 (genuine selected matched weighted quadratic spectral PDE), CI 42529092477 (spectral corrected outer right two C¹), CI 42529333272 (spectral corrected full four-piece C¹), CI 42529503335 (true source-selected spectral corrected full four-piece C¹), plus downstream full Green rechecks. Pending or failed CI is NOT accepted; check actual job logs and exact transitive axioms before claiming success.

**Exact mathematical scope gap:** even simultaneous fixed-time source-selected weighted spectral quadratic defect and corrected physical C¹ interfaces do not yield the original **full four-region nonlocal Hartree PDE** `O(s^(-9/4))` and parameter-Lipschitz estimates on one time-varying orbit. The moving base, Hartree Riesz interaction of the complete corrected fields, the actual parameter time derivatives, complete next-layer source classification, and the finite genuine PDE recurrence are still indispensable. The final Type-II exponent must be obtained from the actual PDE dynamics; no rate is assumed.

**Formal 13-environment revised manuscript acceptance: 11/13 = 84.62%. Neither §2.13 nor the final main theorem is yet closed.**

### November 8 follow-on: exact log diagnostics and genuine common-selector composite

Rechecked original pinned runs directly through GitHub job logs:
[42500440029](https://github.com/penghongzhong/HBL/actions/runs/42500440029) **SUCCESS**, with its downloaded original evidence showing an empty `strict.log` and precise transitive axiom sets `[propext, Classical.choice, Quot.sound]` (possibly universe-annotated) for the two target declarations.
[42501019413](https://github.com/penghongzhong/HBL/actions/runs/42501019413) and
[42501379178](https://github.com/penghongzhong/HBL/actions/runs/42501379178) **FAILURE** with literal old Lean simplification / type rewrite diagnostics. These failures were not retrospectively relabeled successful.

Rechecked the newer workflow jobs. Original
[42527186005](https://github.com/penghongzhong/HBL/actions/runs/42527186005),
[42527710745](https://github.com/penghongzhong/HBL/actions/runs/42527710745),
[42528138223](https://github.com/penghongzhong/HBL/actions/runs/42528138223),
[42528244780](https://github.com/penghongzhong/HBL/actions/runs/42528244780),
[42528244771](https://github.com/penghongzhong/HBL/actions/runs/42528244771),
[42528244857](https://github.com/penghongzhong/HBL/actions/runs/42528244857)
and [42529092477](https://github.com/penghongzhong/HBL/actions/runs/42529092477)
report **SUCCESS**. Of these, the current run independently downloaded the evidence ZIP for
42528138223 and rechecked its empty `strict.log` and standard axiom report;
success of a fixed-time corrected upper repair does not supply the missing true
four-region time-dependent nonlocal source bound.

Actual failure log for
[42528957269](https://github.com/penghongzhong/HBL/actions/runs/42528957269)
isolated `ActualHartreeTrueSourceSelectedWholeMatchedWeighted.lean:147`:
the coupled compatibility definition contains `F0-p1*P1-p2*P2`,
whereas the original selected Green source used `F0+(-p1)*P1+(-p2)*P2`.
The correction in
[commit d5f6c0d](https://github.com/penghongzhong/HBL/commit/d5f6c0d345410ca345c3d89526b6af19390d08cf)
inserts the exact pointwise ring identity in the proof, without adding
a premise or changing the theorem statement.

Actual failure log for
[42529333272](https://github.com/penghongzhong/HBL/actions/runs/42529333272)
isolated unopened `InWeightedL2` namespace and the definitional
difference between a physical Kummer pullback and the corresponding
literal composition `fun y => w(y/a)`.
Both were repaired in
[commit e246d97](https://github.com/penghongzhong/HBL/commit/e246d97dc9e47c88208b5c7ac2ba9812e1f850c5);
the already-successful corrected outer two-C1 CI 42529092477 is a different
certificate.

New actual source-faithful composite
`ActualHartreeTrueSelectedSpectralQuadraticThreeC1.lean` at
[commit 46308fd](https://github.com/penghongzhong/HBL/commit/46308fddc971c148a72a6ffccd46ff4bd0183a62)
forms **one theorem** with the uniquely selected physical real two-speed
simultaneously controlling the source-derived matched weighted quadratic
spectral residual and the corrected three physical C¹ transmission jets.
Its exact-type/axiom pinned CI is
`.github/workflows/hbl-213-true-selected-spectral-quadratic-three-c1.yml`
([commit 10ac46f](https://github.com/penghongzhong/HBL/commit/10ac46f55e97b208d6272d12a9a737d337b96c9c)).
The submitted composite depends on the two upstream proofs; strict success
for it and for the latest repairs is **not yet verified**. The manuscript is
synchronized in [commit 05bb9fa](https://github.com/penghongzhong/HBL/commit/05bb9fa140c98d4fed032e79901ce038b81771d0).
An additional full-Green tactic repair was made at
[commit ac2a603](https://github.com/penghongzhong/HBL/commit/ac2a6034cb91ce9f774f7d0993ff1754ca488de9).

The remaining *genuine mathematical* shortest-path gap is not an algebraic
resummation: the fixed-time selected corrected C¹ field must become a
time-dependent Hartree PDE trajectory, with derived moving Kummer basis
parameter derivatives, true cross-region nonlocal Riesz interactions,
positive-time `s` gain for the **whole** PDE remainder, and exact finite
profile iteration leading to a **derived** Type-II rate. No external
parameter rate, full PDE bound, or spatial matching constant may be silently
inserted as a hypothesis. **Formal original revised environments: 11/13.**


### November 8 22:48 UTC: late CI, pullback repair, and true moving source derivative bridge

New auxiliary CI 42531018033 and 42531018076 both report **Success** (source-faithful matched weighted profile and true selected whole original Green respectively); their new archive axiom output remains to be inspected. CI 42530313725 is the previously strictly certified **generic** spectral-corrected full four-piece three-C1 theorem, artifact 13636899879. Subsequent CI 42531033761 failed at a regression in the physical pullback HasDerivAt elaboration on line 98; commit cd5690848cb1bce924e939249b648dd75015c949 restores exactly the earlier successful proof step. Earlier failed Volterra slope CI 42530358097 had an additive inequality argument-order mismatch on line 108; repaired CI 42531450638 and dependent matched weighted C1 derivative CI 42531500587 remain unaccepted while running. The old selected full-Green CI 42530290819 failed on the same kind of additive term-order error at line 208, repaired and now independently successfully rebuilt in CI 42531018076. The true-source composite C1 and quadratic CIs 42531033768/42531467165/42531467166 remain unaccepted while running.

The actual nonlinear spectral four-piece finite PDE telescope initially failed because of the old imported C1 proof, CI 42530158681. After its dependency was repaired, this theorem was *actually retriggered* by CI 42531641946. The theorem is an exact telescoping *identity*, not a time-positive original Hartree PDE bound.

**New mathematical bridge:** [commit 00dad2b9](https://github.com/penghongzhong/HBL/commit/00dad2b9cec04b956f021a291742a38505dc5335) adds the theorem actual_Hartree_moving_selected_Green_cross_from_physical_time_derivative for the literal time-moving, uniquely Cramer-selected true quartic Hartree source. A pointwise **physical derivative** bound on the actual moving normalized Green source density implies the mixed source/endpoint increment norm <= C |t-s| |R(t)-R(s)| by the mean-value theorem. This replaces an abstract time-Lipschitz assumption with an explicitly traceable *PDE derivative* obligation. The **uniform time derivative estimate on the true PDE orbit remains unproved**, and is not concealed as an assumed time gain. A pinned --trust=0, warningAsError, exact #check, #print axioms with standard-axiom allowlist, no-sorryAx workflow was committed at [74c06cf](https://github.com/penghongzhong/HBL/commit/74c06cfd07a02b704855c5497747554f9c0bd67c), triggering [CI 42532008498](https://github.com/penghongzhong/HBL/actions/runs/42532008498). Manuscript sync: [commit 5ee37784](https://github.com/penghongzhong/HBL/commit/5ee37784af93fe48471ce454731e3c121494433d).

**Formal original revised environments: 11/13 (84.62%).** Still required: original source-derived moving Kummer basis and endpoint/speed derivative budgets, complete four-domain nonlocal time-positive PDE residual and parameter Lipschitz, true finite profile recursion, dynamical Type-II blowup rate.


### Additional original orbit derivative interface: exact Hartree critical scaling and real Cramer differentiation

[Lean a8cf1827](https://github.com/penghongzhong/HBL/commit/a8cf182781d31a3c6440ad941c718fc845d3c8b7) introduces actual_Hartree_true_selected_source_derivative_from_scaled_orbit. It composes the original physical critical Riesz scaling identity F_old(t,r)=a(t)^(-1/2) I_crit(t,r) with the **same real Cramer-selected** speed derivative, producing the full time derivative of F_adj = -F_old - p1*S1 - p2*S2. The derivative of F_old is **no longer a separate hypothesis**; it is derived by the chain/product rule from the actual critically scaled nonlocal interaction and physical a'(t). Source time regularity of I_crit and the actual scale/phase source derivative remain visible PDE-orbit obligations. The Cramer determinant supplies the two real derivatives p1'(t),p2'(t) with the established determinant budget.

The exact pinned CI [42532639028](https://github.com/penghongzhong/HBL/actions/runs/42532639028) was triggered by workflow [74a2bc76](https://github.com/penghongzhong/HBL/commit/74a2bc7652280b4fe8c29db9e3dcf49e84d523f0). It enforces trust=0, warningAsError, full type and exact axioms allowlist; **pending strict completion at submission**. Manuscript synchronized in [3e4b9c2f](https://github.com/penghongzhong/HBL/commit/3e4b9c2fc1f9fd4ac43ac1d99d52e8f0206342ae). This is an auxiliary **physical derivative interface**, not the required positive-time full four-domain residual, so **11/13 unchanged**.

Additional independent auxiliary strict CI Success confirmed: original Volterra weighted value-plus-slope 42531450638, true matched spectral weighted C1 derivative 42531500587, original inverse-linear regular Green density radius gain 42532197451, and one-radius Kummer moment gain 42532387774. Each individual target's archived transitive-axiom report must be audited separately before labelling it an exact-axiom certificate. No auxiliary success increments the original numerator.


### Exact original ZIP evidence audit (2026-11-08): four recent auxiliary targets

Each of the following **original Actions evidence archives was downloaded and opened**, not judged from job titles. All archives contain a zero-byte strict.log, Lean **4.35.0-rc3**, a matching commit hash, the full original source, exact declaration #check output, and individual #print axioms outputs. Every listed target has precisely the transitive standard axiom family **propext / Classical.choice / Quot.sound**, with possible Lean universe annotations and **no sorryAx**.

| CI strictly successful | Original artifact ID | Source commit | Exact exported declarations |
|---|---|---|---|
| [42531450638](https://github.com/penghongzhong/HBL/actions/runs/42531450638) | 13638185198 | 666932dd51c6 | actual_Hartree_zero_left_Kummer_regularized_Volterra_slope_identity; actual_Hartree_zero_left_Kummer_regularized_Volterra_slope_bound; actual_Hartree_zero_left_Kummer_regularized_Volterra_weighted_C1_bound |
| [42531500587](https://github.com/penghongzhong/HBL/actions/runs/42531500587) | 13637228884 | 1efd554ffa20 | actual_Hartree_matched_zero_left_spectral_weighted_C1_response; actual_Hartree_matched_zero_left_spectral_weighted_C1_derivative |
| [42531018076](https://github.com/penghongzhong/HBL/actions/runs/42531018076) | 13637702928 | 5e7832612114 | actual_Hartree_true_source_selected_whole_original_Green_no_radius_loss |
| [42531018033](https://github.com/penghongzhong/HBL/actions/runs/42531018033) | 13637359625 | 5e7832612114 | actual_Hartree_true_source_selected_whole_matched_weighted_no_radius_loss |

The artifact source files contain no actual Lean sorry/admit/axiom declarations (ordinary English use of the word “constant” in module documentation is not a declaration). The pinned workflow explicitly checks Mathlib at **a98628e16c11f5167f16124105ddce53efa9bfe5** and runs --trust=0 with -DwarningAsError=true. These are independent fully audited **auxiliary successes**. The complete evolving physical four-domain PDE remainder, finite recursion, and derived Type-II rate are **not** their conclusion; original 13-environment ledger remains **11/13**.


### Three additional successful independent strict audits: true selected C1, nonlinear PDE telescope, original regular moment

The original successful Actions archive ZIP files were downloaded and inspected: each has an **empty strict.log**, Lean **4.35.0-rc3**, complete #check of the exact exported theorem, and #print axioms with precisely the three standard transitive families **propext, Classical.choice, Quot.sound** and no sorryAx.

| Strict CI | Original artifact | Exact Lean theorem and scope |
|---|---|---|
| [42532174429](https://github.com/penghongzhong/HBL/actions/runs/42532174429) | 13638436296 | actual_Hartree_true_source_selected_spectral_four_piece_three_C1 — the same actual quartic Hartree source, unique real Cramer pair, spectrally corrected physical four-piece field and all three C1 joins |
| [42532174421](https://github.com/penghongzhong/HBL/actions/runs/42532174421) | 13638575634 | actual_Hartree_finite_spectral_Fredholm_four_piece_full_PDE_telescopes — **exact nonlinear background-aware telescoping** of the *full original four-domain nonlocal PDE residual*, including the actual spectral corrected fields and all interactions; proves no individual time-order bound |
| [42532387774](https://github.com/penghongzhong/HBL/actions/runs/42532387774) | 13638131323 | originGreen_inverse_linear_regular_A_moment_difference_radius_gain — original Frobenius mode yields extra radius factor for inverse-linear forcing, without artificial inverse left-radius loss |

In particular, the old telescope CI 42530158681 and its first retrigger 42531641946 both **failed** due to the now-restored correct physical pullback derivative elaboration. The new **same-target** CI 42532174421 succeeds, as does the true-source C1 dependency 42532174429 at commit cd5690848cb1bce924e939249b648dd75015c949. These are not merely hypothetical results. The nonlinear theorem's identity telescopes exact residual *values* and does not yield O(s^-9/4), quantitative parameter Lipschitz, finite physical correction order gain, or dynamically derived Type-II explosion exponent. Mathematical manuscript synchronized in [commit 467f3000](https://github.com/penghongzhong/HBL/commit/467f3000737ae7d22f5c26f6bf4486d773e86994).

**Formal accepted original manuscript environments remain 11/13.** The §2.13 and final theorem still require genuine same-PDE quantitative closure.


### Same unique original Hartree Cramer selector: simultaneous quadratic residual + three corrected C1 interfaces, exact CI

[Strict CI 42532363535](https://github.com/penghongzhong/HBL/actions/runs/42532363535) **Success**, artifact **13638605835**, commit **866bc8edefc9ade33a38c360400674e1f3f8aa2d**. The original ZIP was downloaded and opened. Compiler version exactly Lean **4.35.0-rc3**; strict.log **0 bytes**; full elaborated #check target **actual_Hartree_true_source_selected_spectral_quadratic_and_three_C1**; #print axioms reports **only** propext, Classical.choice, Quot.sound, with no sorryAx. The proof relates one and the same physical quartic Riesz Hartree source and unique real two-dimensional Cramer speed to a source-derived matched-weighted quadratic spectral Kummer defect AND corrected physical C1 transmission at all three joins.

The weighted envelope is obtained from original Cramer/Green data rather than newly postulated. Nevertheless, **no derived time power for the spectral displacement**, moving basis full source, nonlinear four-region residual O(s^-9/4), physical finite recursion, or Type-II dynamical blowup law follows. It remains an accepted **auxiliary**, not original §2.13. Paper synchronized at [4cded3ed](https://github.com/penghongzhong/HBL/commit/4cded3edce4a608d4382dd9590a3477f4ea2432e). Formal original count: **11/13**.

### 2026-11-09: real strict-error repairs and physical radial-slope scope audit

The branch's next two source-bearing candidates failed in *their original GitHub job logs*, not from paper bookkeeping:

- [CI 42532993719](https://github.com/penghongzhong/HBL/actions/runs/42532993719) — **failure** at `ActualHartreeSelectedSourceDerivativeFromScaledOrbit.lean:87`: Lean distinguishes the function-level minus `-(fun t => F t)` from the pointwise minus `fun t => -F t` before simplification. [Commit dbf9c083](https://github.com/penghongzhong/HBL/commit/dbf9c083404cb395720a2071161ad7b9516426af) repairs the exact target by adding `Pi.neg_apply`. Strict CI [42535448152](https://github.com/penghongzhong/HBL/actions/runs/42535448152) is a **new verification run**, not counted accepted before its own result and axiom audit.
- [CI 42532790432](https://github.com/penghongzhong/HBL/actions/runs/42532790432) — **failure** of the unweighted zero-left Volterra slope theorem at five real elaboration/inequality steps: `trans_le` misuse, reversed additive ordering, unspecified norm-add arguments, additive ordering in the quartic reduction, and invalid `mul_le_mul_left` use. [Commit 642d79e3](https://github.com/penghongzhong/HBL/commit/642d79e3be862c6ba362fbc9969eaeb8128d2e8f) repairs those actual proof lines, and strict CI [42535477786](https://github.com/penghongzhong/HBL/actions/runs/42535477786) is **running/pending at submission**, so not yet certified.

Previously pending [CI 42533177432](https://github.com/penghongzhong/HBL/actions/runs/42533177432) now reports **Success** for `actual_Hartree_moving_selected_Green_cross_from_physical_time_derivative`, deriving the mixed source/endpoint increment estimate from the **explicit original physical source-density time-derivative bound**. The latter is not yet obtained in uniform quantitative weighted norm from the full PDE orbit; this is a conditional physical derivative interface, not a complete time-gain theorem.

**Crucial source-scope distinction:** the zero-left unweighted derivative theorem is proved under an inverse-linear pointwise source `||F(r)|| <= M/r`; the original Hartree source producer initially supplies an inverse-square `||F_0(r)|| <= Q/r^2` together with a sharper *scaled* `(1+a r)^(-19/8)` envelope, and the real selected speed generators have a *different* inverse-linear envelope. The stronger inverse-linear hypothesis cannot simply be assigned to the whole original adjusted source with a radius-independent `M`. The next Hdot1 producer should split genuine original and selected-speed sources and use the scale-sharp Riesz regular coefficient already verified. Pointwise unweighted `u'(r)` control is strictly stronger than the radial energy norm and need not be promoted to a required premise of §2.13.

**Formal revised original scope: 11/13.** No new §2.13 acceptance, no claimed full four-domain time-positive Hartree residual, no dynamically derived Type-II exponent.

### Confirmed strict success from the original evidence: inverse-linear zero-left unweighted slope

[CI 42535477786](https://github.com/penghongzhong/HBL/actions/runs/42535477786) **SUCCESS** at commit `642d79e3be862c6ba362fbc9969eaeb8128d2e8f`. Original [evidence artifact 13639651318](https://github.com/penghongzhong/HBL/actions/runs/42535477786/artifacts/13639651318) downloaded, decompressed and directly inspected: `strict.log` **0 bytes**; `audit.log` includes exact `#check @HBL.TypeIIDynamicSelection.actual_Hartree_zero_left_Kummer_Volterra_unweighted_slope_no_left_radius`; full transitive `#print axioms` is **exactly** `[propext, Classical.choice, Quot.sound]`; verified Lean 4.35.0-rc3 and pinned Mathlib source from the workflow; no `sorryAx`. The bound is valid for the inverse-linear class `‖F(r)‖ ≤ M/r`, and remains an auxiliary theorem, **not** a substitute for the inverse-square original Riesz source or §2.13 global PDE proof.

The new actual-original quartic Riesz radial-energy candidate `ActualHartreeOriginalRieszZeroLeftEnergySlope.lean` was committed at `95fb3ec6` and has its own isolated strict `--trust=0` run(s) [42536398545](https://github.com/penghongzhong/HBL/actions/runs/42536398545) / [42536419967](https://github.com/penghongzhong/HBL/actions/runs/42536419967); **these are pending at the time of this bookkeeping entry**. Its conclusion is an `r‖u'_0(r)‖` estimate for the actual Riesz source, with the second Green moment derived from the genuine `L^(-3/8)` physical tail. The additional source-continuity premise has since been **eliminated** in commit `5bc59e00366130deed26df68a6758af3a553505e`: the exact moment splitting now uses interval integrability of the original Riesz source and the authentic Kummer Green density, both supplied by existing producer theorems (new strict replay still required). This changes no original environment count.

**Original archive check for the moving physical Green derivative.** Downloaded and directly inspected [CI 42533177432 evidence 13638766564](https://github.com/penghongzhong/HBL/actions/runs/42533177432/artifacts/13638766564), at source commit `b5cf627d40187ab4e20b7b666860ff0f0bcda5aa`: `compiler-version.txt` = Lean 4.35.0-rc3, `strict.log` = **0 bytes**, complete `#check @actual_Hartree_moving_selected_Green_cross_from_physical_time_derivative` present, transitive `#print axioms` = exactly `[propext, Classical.choice, Quot.sound]`. This authenticates a mixed physical source/endpoint derivative identity; it does **not** derive an independent positive-time remainder norm.

### 2026-11-09: same-physical-source derivative and zero-left radial-energy bridge

Three already submitted strict jobs have now been **individually certified from their original GitHub evidence ZIPs**, with Lean 4.35.0-rc3, exact `#check @...`, nonempty full-type `audit.log`, empty `strict.log` and transitive `#print axioms = [propext, Classical.choice, Quot.sound]`:

- [42536615928](https://github.com/penghongzhong/HBL/actions/runs/42536615928), [original evidence 13640116712](https://github.com/penghongzhong/HBL/actions/runs/42536615928/artifacts/13640116712), commit `efd2d7054edccbd9966467614df48d43726ac722`: `actual_Hartree_true_selected_source_derivative_from_scaled_orbit`. This differentiates the true critically-scaled quartic Hartree source and selected two real Cramer speeds from the original scaled-orbit derivative interface; it does **not** establish the requisite quantitative weighted source-time norm from an original PDE trajectory.
- [42536770197](https://github.com/penghongzhong/HBL/actions/runs/42536770197), [original evidence 13640460945](https://github.com/penghongzhong/HBL/actions/runs/42536770197/artifacts/13640460945), commit `807b9e5081a7`: `actual_Hartree_one_orbit_original_Riesz_produces_selected_source_derivative`. Distinct physical three-Riesz derivative producer; again the exact type retains explicit trajectory regularity/derivative hypotheses, not a proven time-positive PDE residual.
- [42536552509](https://github.com/penghongzhong/HBL/actions/runs/42536552509), [original evidence 13639851938](https://github.com/penghongzhong/HBL/actions/runs/42536552509/artifacts/13639851938), commit `0b68980a4033a9a8e69ea87bba3a31f0d5eb2591`: `actual_Hartree_finite_spectral_Fredholm_four_piece_full_PDE_telescopes` under the already physical four-zone field constructor. This is **nonlinear residual telescoping equality, NOT a quantitative time-order estimate**. Original environment 11/13 unchanged.

**New main-chain source-specific energy construction** (new strict replay still pending):

- `ActualHartreeOriginalRieszZeroLeftEnergySlope.lean`, initial `95fb3ec6`, improved `5bc59e00` (removed independent source continuity, deriving integrability from original Hartree), corrected **actual original job-log errors** at `c3493467`: first use the exact `originGreenWronskian_exact` instead of rewriting the wrong physical Wronskian expression; then use `add_le_add` in the correct order for the regular-mode cubic estimate. Latest strict [42537256831](https://github.com/penghongzhong/HBL/actions/runs/42537256831) is pending. Old [42536398545](https://github.com/penghongzhong/HBL/actions/runs/42536398545), [42536419967](https://github.com/penghongzhong/HBL/actions/runs/42536419967), [42536768683](https://github.com/penghongzhong/HBL/actions/runs/42536768683) **failed**, were read, and are **not** acceptance.
- `ActualHartreeZeroLeftInverseSquareEnergySlopeCore.lean` at `de42b6c8`, locked strict [42537615993](https://github.com/penghongzhong/HBL/actions/runs/42537615993), is a SOURCE-CLASS mathematical lemma deriving the Cramer cancellation `‖A(r)-A(r0)‖≤JQ(r-r0)` and `r‖actualOriginMatchedKummerSlope‖≤(B+1)GJQ+2(D+1)GB²T`. By itself its source envelope and regular B coefficient are assumptions; **the actual PDE cannot invoke this standalone as an independent residual bound**.
- `ActualHartreeTrueSourceSelectedZeroLeftEnergySlope.lean` at `5af3e281`, workflow `b0fc4625`, strict [42537783978](https://github.com/penghongzhong/HBL/actions/runs/42537783978), **explicitly discharges both source-class inputs from the SAME physical Hartree/Cramer producers** `actual_Hartree_true_source_selected_corrected_inner_and_outer_norm` and `actual_Hartree_true_source_selected_adjusted_regular_Green_all_radii`, uses the **same uniquely compatible real two-speed** (equality by the actual uniqueness theorem), derives integrability of the combined source and its own finite B-channel bound `T`, then applies the generic zero-left radial-energy lemma. Its strict status is **pending**, NOT accepted. This path introduces no externally stipulated inverse-linear bound, no guessed positive time order and no Type-II blowup rate.

**Subtle differentiability audit:** `actualOriginMatchedKummerSlope` is the **algebraically defined Kummer Green slope**. With merely `Measurable z`, the theorem as stated bounds that expression, not automatically a pointwise classical `deriv` of the integrated field. Identification with the genuine radial derivative must be obtained through a classical source/PDE regularity bridge or a suitable a.e. Sobolev identification. We will not silently strengthen the exact Lean type or manuscript C¹ meaning.

**Original unchanged**: 11/13. §2.13 still lacks a same-PDE full four-region positive-time nonlocal residual with quantitative parameter Lipschitz and genuine finite recursion. Final Type-II exponent must be dynamically derived.

### Strict source-energy replay errors actually corrected (2026-11-09 UTC)

- The full original-source [42537256831](https://github.com/penghongzhong/HBL/actions/runs/42537256831) **FAILED** at `ActualHartreeOriginalRieszZeroLeftEnergySlope.lean:265`: `Unknown identifier exact` because the proof branch used `:= exact` instead of `:= by exact`. **Fixed** in [d6292101](https://github.com/penghongzhong/HBL/commit/d62921015e51312d71d6e1c20fbb3d59a1d124a4); new strictly pinned [42538089908](https://github.com/penghongzhong/HBL/actions/runs/42538089908) triggered, not certified before evidence check.
- The generic inverse-square Cramer core [42537615993](https://github.com/penghongzhong/HBL/actions/runs/42537615993) **FAILED** at :58 on `dsimp [T]`: `T` is a parameter, not a local definition. The proof also inherited the `:= exact` parser error. **Fixed** in [679d08c7](https://github.com/penghongzhong/HBL/commit/679d08c74397fdc7cb43b0c855c7cc906e213298) and [16ac5673](https://github.com/penghongzhong/HBL/commit/16ac56732fc49c116081df8daeac3cb5286e45e1); new strictly pinned [42538394751](https://github.com/penghongzhong/HBL/actions/runs/42538394751) triggered, not yet certified.
- The **same-source physical selected** wrapper has been strengthened to explicitly instantiate the genuine scale/phase-source integrability factors and correct source sum associativity in [7bdd26fd](https://github.com/penghongzhong/HBL/commit/7bdd26fde88bef2d9fcd541fa5111b58af21baa9), and to derive `|c|≤1` from the physical smallness `a|c|≤ε≤1` and `a≥1` by a proven nonnegative product in [6ee279c2](https://github.com/penghongzhong/HBL/commit/6ee279c290637a2ef1482f8d6ef8af5124e79896). Latest new strict [42538448446](https://github.com/penghongzhong/HBL/actions/runs/42538448446) is in progress; do not count this wrapper until it compiles, its exact type is extracted and its original transitive axiom evidence is checked.

The core/source-specific distinction and formal-slope-vs-classical-derivative issue documented above remain mandatory. Original environment acceptance **11/13**.

### Physical original quartic Riesz zero-left energy slope STRICT SUCCESS (2026-11-09)

[GitHub Actions 42538089908](https://github.com/penghongzhong/HBL/actions/runs/42538089908), committed source `d62921015e51312d71d6e1c20fbb3d59a1d124a4`, **SUCCESS**. Original [evidence ZIP 13640232684](https://github.com/penghongzhong/HBL/actions/runs/42538089908/artifacts/13640232684) was downloaded and inspected directly: `strict.log` **0 bytes**; Lean **4.35.0-rc3**; exact `#check @HBL.TypeIIDynamicSelection.actual_Hartree_original_Riesz_zero_left_energy_weighted_slope_no_left_radius` present (full type); transitive `#print axioms` **exactly `[propext, Classical.choice, Quot.sound]`**; no `sorryAx`. Workflow pins Mathlib commit `a98628e16c11f5167f16124105ddce53efa9bfe5`, invokes `lake env lean --trust=0 -DwarningAsError=true`.

**Actual mathematical conclusion:** using the real quartic Riesz source `F₀=-a² S_H(ar)` with the genuine physical `Q` and original no-loss coefficient `T= (8/3) G Q L^{-3/8}`, exact Wronskian cancellation yields
`r ‖actualOriginMatchedKummerSlope(K,L/a,B,F₀,0,0,r)‖ ≤ (B+1)G(1+(D+1)GB²)Q + 2(D+1)GB² T` on `L/a ≤ r ≤ B`, without negative powers of the left radius. Source integrability and both physical size/tail inputs were **proved from the original Riesz source**, not postulated independently. This is the ORIGINAL unadjusted quartic source and zero-left jet; the **uniquely selected modulation-adjusted source**, full Fredholm left jet and four-region time-gain still require their distinct producer theorem. It bounds the named algebraic Kummer slope, not automatically the classical derivative for arbitrary measurable radiation.

**Original environments: 11/13**, this newly certified result is an auxiliary theorem, not full §2.13. Distinct source-selected [42538448446](https://github.com/penghongzhong/HBL/actions/runs/42538448446) and inverse-square core [42538394751](https://github.com/penghongzhong/HBL/actions/runs/42538394751) were **pending** at this ledger revision.

### Strict original Riesz zero-left radial-energy producer ACCEPTED — 42538089908

Original independent [CI 42538089908](https://github.com/penghongzhong/HBL/actions/runs/42538089908) **SUCCESS**, source commit `d62921015e51312d71d6e1c20fbb3d59a1d124a4`, downloaded [evidence artifact 13640232684](https://github.com/penghongzhong/HBL/actions/runs/42538089908/artifacts/13640232684). Direct ZIP readback: `strict.log` **0 bytes**; exact target `#check` and `#print axioms` present; transitive `[propext, Classical.choice, Quot.sound]` only; no `sorryAx` or `admit`; pinned Lean 4.35.0-rc3 and source SHA256 `d2972d767914c1c58c8c1ba65bd71f7d81a65d810d4507c730ea27c9f3c5e406`.

Verified target `actual_Hartree_original_Riesz_zero_left_energy_weighted_slope_no_left_radius` applies to the `genuine original quartic Hartree Riesz source` `F0(r)=-a² S_H(ar)`, deriving both inverse-square envelope and nonlocal regular-channel original Green moment. For `J=1+(D+1)GB²`, `Q=C_phys*ell^(1/8)`, `T=(8/3)*G*Q*L^(-3/8)`, it proves `‖(r:ℂ)*actualOriginMatchedKummerSlope K (L/a) B F0 0 0 r‖ ≤ (B+1)*G*J*Q+2*(D+1)*G*B²*T` for each original physical matching radius. **No explicit 1/(L/a) loss**. This is the algebraic Green slope, not (under merely measurable radiation) an automatically certified classical radial derivative.

**Important scope:** this exact success is for **F0**, not yet the uniquely selected **Fadj=F0-p₁S₁-p₂S₂**. The dedicated combined genuine-source unique Cramer speed theorem `ActualHartreeTrueSourceSelectedZeroLeftEnergySlope.lean` has separate CI [42538448446](https://github.com/penghongzhong/HBL/actions/runs/42538448446) still requiring its own success and axiom audit. No physical weighted time-order or global four-piece PDE gain is inferred; revised manuscript remains **11/13 (84.62%)**.

### Strict inverse-square zero-left Kummer radial-energy core ACCEPTED — 42538394751

[CI 42538394751](https://github.com/penghongzhong/HBL/actions/runs/42538394751) **SUCCESS** at commit `16ac56732fc49c116081df8daeac3cb5286e45e1`, original evidence artifact [13640169734](https://github.com/penghongzhong/HBL/actions/runs/42538394751/artifacts/13640169734) independently downloaded and read. `strict.log` empty, Lean 4.35.0-rc3, exact type `#check @HBL.TypeIIDynamicSelection.actual_Hartree_zero_left_inverse_square_energy_slope_core`; full transitive `#print axioms` is precisely `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. Source SHA256 `2a755c179e0fa53cf31d4b741190d8a75cb1071cdcfb7dd6d5b1f10e4ae36f7a`.

This **source-class** lemma derives `r‖S_K[F](r)‖≤(B+1)GJQ+2(D+1)GB²T` for inverse-square forcing `‖F(r)‖≤Q/r²` and regular Green moment `‖B_F(r)‖≤T`. Neither `Q` nor `T` is an independent physical Hartree theorem assumption; the strict original Riesz producer and the same unique selector must supply them. The exact SAME-SELECTOR physical wrapper `ActualHartreeTrueSourceSelectedZeroLeftEnergySlope.lean` remains under separate CI [42538448446](https://github.com/penghongzhong/HBL/actions/runs/42538448446) and its own axiom audit; no acceptance until success. Formal main environment **11/13**.

### New same-selector radial energy and spectrally corrected three-C1 bridge (strict pending)

[Commit e876f28c](https://github.com/penghongzhong/HBL/commit/e876f28c4669e943708fcbfd2a395a53e1d9e5df), source `ActualHartreeTrueSelectedEnergySlopeSpectralThreeC1Joint.lean`, directly joins the **same uniquely compatible real Cramer pair** supplied by the physical adjusted-Hartree zero-left energy slope and the existing `actual_Hartree_true_source_selected_spectral_four_piece_three_C1` theorem. It explicitly proves the equality of the two real selector outputs by the original uniqueness theorem, never assumes a separate interface speed. The output retains both (i) `r‖actualOriginMatchedKummerSlope(K,r0,B,Fadj,0,0,r)‖ ≤ ...` with no inverse `r0` and physical (Q_a,T) producers, and (ii) the **spectral-corrected**, physical four-piece field's literal three `HasDerivAt` joins at `L,aB,2aB`, under its visible original source-continuity premise. This is **fixed-time**; full corrected field `Hdot1`, time-positive PDE remainder, parameter Lipschitz and finite nonlinear induction are still missing. Locked `--trust=0` exact-type/axioms CI [42539718869](https://github.com/penghongzhong/HBL/actions/runs/42539718869) **PENDING** (not accepted before evidence). No count change: 11/13.

### Decisive dynamic-gain audit: shell positive-time lemma still depends on a decay trap

Direct source audit of `HBL/TypeIIDynamicSelection/ActualHartreeOneOrbitFullShellSharp.lean` confirms the **genuine original PDE** shell commutator (including moving cutoff and true nonlocal quartic Riesz) has source-derived size `C·ell(s)^2·sqrt(ell(s)) = C ell(s)^(5/2)` under the physical flux/Strauss hypotheses, with the true moment-radius drift `R_s/R-b = -ell(s)^2 m'(t)/m`. This is a legitimate *physical scale* gain.

However `ActualHartreeOneOrbitFullShellTimeGain.lean`, theorem `actual_Hartree_one_orbit_full_shell_positive_time_order`, STILL explicitly requires
`(htrap : ell s ≤ s ^ (-beta))` and `(hbeta : 1/2 < beta)`, only then converting `ell(s)^(5/2)` to `s^(-1-(5 beta / 2-1))`. **That is not yet a deduction from the actual orbit PDE.** It may be an intermediate bootstrap condition but is categorically **not permitted as a final §2.13 or Type-II theorem assumption** under this project's acceptance rules. It cannot be used as evidence of a derived time order until its entry-and-persistence dynamics (or a rate-free integrable scale mechanism) are strictly closed.

This is the concrete current math bottleneck behind the remaining full four-domain time-positive residual: need PDE-produced `ell,b,modulation` dynamics and source/endpoint quantitative parameter Lipschitz, and a verified induction in the resulting scale without assuming the Type-II rate. The strict identity `actual_Hartree_finite_spectral_Fredholm_four_piece_full_PDE_telescopes` is still only an equality. Original score stays **11/13**.

### Rate-free original PDE-shell clock bridge (strict replay pending)

An alternative to the forbidden unproved `ell(s)≤s^{-beta}` trap has now been implemented in `ActualHartreeOneOrbitFullShellClockGain.lean` (commit [3913342b](https://github.com/penghongzhong/HBL/commit/3913342bf9d1077ffd713c5086cae89fec4869c2)). For the **real original nonlocal Hartree PDE shell** `actual_Hartree_one_orbit_full_shell_from_PDE_moment_and_Strauss`, the established `‖E_shell(s,r)‖≤C ell(s)² sqrt(ell(s))`, coupled to the **actual** physical renormalization `HasDerivAt time (ell(s)²) s` and the small-scale range `0<ell(s)≤1`, yields the **rate-free physical clock density control**
[
\|E_{\rm shell}(s,r)\|\le C\,\ell(s)^2\sqrt{\ell(s)}
\le C\,t_s(s)=C\,\frac{dt}{ds}.
]
The clock derivative is produced from the same orbit kinematics, **not** a guessed (s^{-\rho}) residual order. Under an eventual finite physical horizon (t(s)\uparrow T), integrating this *would* yield \(\int_s^\infty \|E_{\rm shell}(\sigma,r(\sigma))\|d\sigma\le C(T-t(s))\) once integrated shell measurability/uniform spatial control are certified; the finite horizon and full four-domain residual are **not** proved by this new pointwise theorem. This avoids forcing a Type-II exponent *at the shell conversion step* but does not replace the full dynamical closure. Exact source type and axiom workflow [CI 42540076575](https://github.com/penghongzhong/HBL/actions/runs/42540076575) **pending** at submission. Original count 11/13.

### 2026-11-09: genuine Cramer-selected zero-left energy AND exact full matched outgoing trace — strict successes

- [CI 42539393349](https://github.com/penghongzhong/HBL/actions/runs/42539393349): **SUCCESS**, target `actual_Hartree_true_source_unique_speed_zero_left_energy_slope`, commit `7c73f6d35e0f797855a40218bcb10c81d0e6bf68`. Original [artifact 13641321478](https://github.com/penghongzhong/HBL/actions/runs/42539393349/artifacts/13641321478) directly unzipped and audited: `strict.log` = 0 bytes, Lean 4.35.0-rc3, exact `#check`, and exactly `[propext, Classical.choice, Quot.sound]` with no `sorryAx`; source hash `f2387aa20ec5236ea07715f7944d72b1465984b6946b20849a244434c3cfecdc`. The genuine original nonlocal Hartree Riesz source generates the **unique** real Cramer speed, original adjusted inverse-square envelope `Qa≤Cn*(N+Q)`, and same selected regular Green moment `T=((8/3)*G*Q)*L^(-3/8)+(Csp*G*B*Csel)*(N+Q)`. Therefore the original selected adjusted zero-left Kummer slope has the strict bound `‖r*Slope[Fadj;0,0]‖≤(B+1)*G*J*Cn*(N+Q)+2*(D+1)*G*B²*T`, no explicit inverse left radius. It is *not* yet the complete full matched Cramer slope with Fredholm left jet.
- [CI 42539730025](https://github.com/penghongzhong/HBL/actions/runs/42539730025): **SUCCESS**, target `actual_Hartree_matched_slope_zero_left_plus_original_jet_exact`, commit `a243ff40e80fe2161dd17cde7481b1804db2d093`. Original [artifact 13641645473](https://github.com/penghongzhong/HBL/actions/runs/42539730025/artifacts/13641645473): `strict.log` empty, exact proof and the same three standard transitive axioms, no `sorryAx`; source hash `3e9a134c5139113699e92507c3d6dc231957621c3f8fcd84d2e0dbd5c84c958d`. Under actual compatibility the **FULL matched slope** equals `Slope[F;0,0] + J_-(r0)*Y'(r) + gamma*X'(r)`. It is mathematically incorrect to omit the physical Fredholm outgoing trace just because the separate homogeneous singular coefficient is zero.

The full matched original-trace `r\|Slope\|` estimate has its own [CI 42540031173](https://github.com/penghongzhong/HBL/actions/runs/42540031173); the **physical selected full matched** wrapper has [42540289263](https://github.com/penghongzhong/HBL/actions/runs/42540289263); and the a.e.-derivative, true 3D radial Hdot1 integral has [42540682351](https://github.com/penghongzhong/HBL/actions/runs/42540682351). These latter three must be reported as **PENDING** until independently successful with exact axiom archives. The original **13-environment count stays 11/13**, with the four-region positive-time original nonlinear residual, feedback Lipschitz, finite generated-source recursion, and dynamically derived Type-II law still open.


### 2026-11-09 independent CI replay and physical-clock lint correction

Checked live branch GitHub Actions and the original job logs (not just filenames). Four previously failing strict C1/PDE jobs now have subsequent **successful** locked jobs:

- [42532174427](https://github.com/penghongzhong/HBL/actions/runs/42532174427): `actual_Hartree_spectral_inner_four_piece_three_C1_joins`, corrected physical four-piece *three* C1 interfaces;
- [42532174429](https://github.com/penghongzhong/HBL/actions/runs/42532174429): `actual_Hartree_true_source_selected_spectral_four_piece_three_C1`, same genuine selected original Hartree source;
- [42532363535](https://github.com/penghongzhong/HBL/actions/runs/42532363535): `actual_Hartree_true_source_selected_spectral_quadratic_and_three_C1`;
- [42536552509](https://github.com/penghongzhong/HBL/actions/runs/42536552509): `actual_Hartree_finite_spectral_Fredholm_four_piece_full_PDE_telescopes`, *exact* nonlinear difference-of-residuals finite sum. In this run the original job explicitly reported transitive axioms **[propext, Classical.choice, Quot.sound]**, under `lake env lean --trust=0 -DwarningAsError=true`, target `#check` and target `#print axioms`; artifact **13639851938**.

Also independently confirmed actual original-source and no-left-radius results [42539393349](https://github.com/penghongzhong/HBL/actions/runs/42539393349) (same unique compatible Cramer selector), [42539718869](https://github.com/penghongzhong/HBL/actions/runs/42539718869) (same selector plus corrected three-C1), and [42539730025](https://github.com/penghongzhong/HBL/actions/runs/42539730025) (full algebraic matched slope including nonzero original outgoing Fredholm trace), all with strict jobs **SUCCESS**. The last assertion is an algebraic radial slope, not yet a derived a.e. radial derivative or global Hdot1 estimate.

The first rate-free physical-clock shell CI **42540076575 FAILED** on the *actual* diagnostic `ActualHartreeOneOrbitFullShellClockGain.lean:39:5: Variable name hell is not explicitly referenced` (strict warning-as-error); it was a linter error, **not** an analytical counterexample. The local proof now uses `pow_nonneg hell.le 2` to prove the nonnegative clock factor, source commit [9745d3b](https://github.com/penghongzhong/HBL/commit/9745d3bdfd14e65ba8835a31c579f7e2f3ae38c7), with replacement strict job [42540898273](https://github.com/penghongzhong/HBL/actions/runs/42540898273). **No Success claimed until this replacement completes.** Distinct full matched energy and classical Hdot1 replays 42540031173, 42540289263, 42540682351 likewise remain pending until checked.

**Non-circular §2.13 obstruction:** a nonlinear PDE residual telescope is only an identity; rate-free moving-shell `C ell^2 sqrt(ell)` has not yet been turned into a uniform *spatial*, *four-domain* time-integrable bound for the same actual orbit with a PDE-established finite physical horizon and quantified modulation/endpoint Lipschitz estimates. In particular no `ell(s) ≤ s^(-beta)`, positive-order remainder, finite recurrence, or Type-II blowup rate may be silently assumed. **Formal revised 13-environment acceptance remains 11/13 (84.62%); §2.13 and final theorem OPEN.**

### Strict original compatible matched Kummer radial H1 energy: 42541312630

[CI 42541312630](https://github.com/penghongzhong/HBL/actions/runs/42541312630) — **SUCCESS** on source commit `8b5c101887b24c068af3bd0311a7cfa64a4ea76a`; exact original [evidence artifact 13641453753](https://github.com/penghongzhong/HBL/actions/runs/42541312630/artifacts/13641453753) downloaded and inspected. `strict.log` 0 bytes, Lean 4.35.0-rc3, exact `#check @HBL.TypeIIDynamicSelection.actual_Hartree_full_matched_radial_H1_from_original_trace`, `#print axioms=[propext,Classical.choice,Quot.sound]`, no `sorryAx`. Source SHA256 `2a1158522948ce3a2a0e1332a8ef9c6c361bb4cf06501f9cd19863e530519d3b`.

The theorem invokes the already formalized `actual_origin_matched_Kummer_certificate_iff`, **which identifies the algebraic matched Green slope with the actual derivative almost everywhere** from real source `IntervalIntegrable F` and compatibility, with *no source continuity premise*. Combining the verified full-matched trace reduction and the 3D radial measure yields `∫_{a}^{b} r² ‖deriv W r‖² dr ≤ (b-a) Efull²`, where `Efull = Ezero+(b+1)G Ct+2(D+1)G²b²(a‖DU‖+(a+1)‖U‖)`, under source-origin trace budget `‖J_-‖≤Ct*a`.

This is now a **strictly accepted true derivative & energy integral** for compatible original Kummer fields, not a purely formal slope; however `hZero` and `hTrace` are its *visible inputs*, rather than a complete same-source physical bound. The physical source-locked downstream `ActualHartreeTrueSelectedFullMatchedRadialH1.lean` was submitted with strict [42541621509](https://github.com/penghongzhong/HBL/actions/runs/42541621509) and must separately pass. Original manuscript remains **11/13**, no full all-region nonlinear time gain or final Type-II law.

### Original Fredholm outgoing trace cancellation gives full matched radial energy — 42541312505 strictly accepted

[CI 42541312505](https://github.com/penghongzhong/HBL/actions/runs/42541312505) is **SUCCESS** on exact source commit `8b5c101887b24c068af3bd0311a7cfa64a4ea76a`; independently downloaded [original artifact 13641279788](https://github.com/penghongzhong/HBL/actions/runs/42541312505/artifacts/13641279788), Lean 4.35.0-rc3, empty `strict.log`, actual `#check` of `actual_Hartree_full_matched_radial_energy_from_zero_left_and_jet`, exact transitive axioms `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. Source SHA256: `371bf72e92a86876710a1ff15143eb3d6a9b0bf57778337ed46f1a6dbb184c0c`.

Its conclusion is the **full** matched Green *algebraic* slope, not the zero-left surrogate: if the zero-left source response has `‖r S0(r)‖≤E`, actual Fredholm outgoing trace obeys `‖J_-(a)‖≤Ct*a`, and the same actual compatibility matches the left jet `(U,DU)`, then `‖r S[F;U,DU](r)‖ ≤ E+(b+1)G*Ct+2(D+1)G²b²(a‖DU‖+(a+1)‖U‖)`. No inverse power of moving left radius occurs because `a/r≤1` exactly. **This is a fixed-slice generic physical Green/trace estimate; the source-specific realization of both E and Ct by the same original Hartree/Cramer pair is separately under [CI 42541312631](https://github.com/penghongzhong/HBL/actions/runs/42541312631), and its a.e. `Ḣ¹` integral has [42541621509](https://github.com/penghongzhong/HBL/actions/runs/42541621509) pending. Original manuscript 11/13 unchanged.**

### Rate-free genuine Hartree shell physically integrated through its original clock: 42541952006

[CI 42541952006](https://github.com/penghongzhong/HBL/actions/runs/42541952006) **SUCCESS** on exact source commit `8709737a5221443d212cab6304e45372d47956da`; original [evidence 13641333733](https://github.com/penghongzhong/HBL/actions/runs/42541952006/artifacts/13641333733) downloaded and inspected. Pinned compiler Lean 4.35.0-rc3, `strict.log` empty, exact `#check @HBL.TypeIIDynamicSelection.actual_Hartree_shell_integrated_physical_clock_no_beta`, transitive `#print axioms=[propext,Classical.choice,Quot.sound]`, no `sorryAx`, SHA256 source `663ccb0acb550b1ebddee6fd590a99fc9f0b2af18183451bf94f4f699a9f7a93`.

From **actual differentiable modulation orbit** `ell'(s)=-b(s)*ell(s)`, `time'(s)=ell(s)^2`, `0<ell(s)≤1` on `[s0,s1]`, proves `∫_{s0}^{s1} ell(s)^2*sqrt(ell(s)) ds ≤ time(s1)-time(s0)` without ANY `ell(s)≤s^(-beta)` or prescribed Type-II rate. The source file includes a fixed-nonnegative-coefficient corollary, compiled in the same full strict file check. This closes the scalar integrated factor of the genuine physical shell theorem **conditional on the actual orbit**; it does **NOT** yield finite physical terminal time, uniform full four-region error, nonlinear generated-source classification, finite recursion or derived blowup speed. Formal revised count **11/13**.

### Original Hartree unique-selector full matched radial H1 strict COMPLETION — 42541312631 and 42541621509

Previously pending runs **now independently confirmed** from their source-locked original ZIP archives:

- [CI 42541312631](https://github.com/penghongzhong/HBL/actions/runs/42541312631) **SUCCESS**, source commit `8b5c101887b24c068af3bd0311a7cfa64a4ea76a`, original [artifact 13642007254](https://github.com/penghongzhong/HBL/actions/runs/42541312631/artifacts/13642007254); exact target `actual_Hartree_true_selected_full_matched_radial_energy_no_left_radius` in `ActualHartreeTrueSelectedFullMatchedRadialEnergy.lean`, source SHA256 `f6e64f7b42a37270255fbd76a844907fa659d5db50314d1bea1f0490ab15d417`. Empty `strict.log`, compiler 4.35.0-rc3 and exact standard transitive axioms only, no `sorryAx`.
- [CI 42541621509](https://github.com/penghongzhong/HBL/actions/runs/42541621509) **SUCCESS**, source commit `62ce5d296c8c51f18540f0773e9bbfab4042f71d`, original [artifact 13641534753](https://github.com/penghongzhong/HBL/actions/runs/42541621509/artifacts/13641534753); target `actual_Hartree_true_selected_full_matched_radial_H1_no_left_radius` in `ActualHartreeTrueSelectedFullMatchedRadialH1.lean`, source SHA256 `070e0afe548ccaa748bc50dc70a69eb7de25d1b64fccb7d9e6d69b7717f6e5d5`; empty strict log, exact source type and precisely `[propext, Classical.choice, Quot.sound]` without `sorryAx`.

This is the critical *genuine physical source* closure of the chain **original three-Riesz Hartree source -> unique real Cramer p -> actual corrected two Fredholm channels and canonical left jet -> full zero-left plus outgoing/regular Cramer matched Kummer radial slope -> actual a.e. derivative -> normalized annular 3D weighted energy integral**:
`∫_{L/a}^{B} r² ‖deriv W_selected(r)‖² dr ≤ (B-L/a)*Efull²`.
Both the selected `p` and the quantitative `Efull` come from the SAME original nonlocal interaction and Fredholm data, not supplied as arbitrary regional speed/energy hypotheses. No explicit negative power of `L/a` occurs in the bound.

**Non-vacuous integrability audit:** the exact printed 42541621509 theorem concludes an integral inequality, while the native a.e. certificate separately produces continuous algebraic slope. To make explicit `IntegrableOn (r²‖deriv W(r)‖²)` in the kernel-checked statement, `ActualHartreeMatchedRadialH1Integrable.lean` was separately submitted to [CI 42542447894](https://github.com/penghongzhong/HBL/actions/runs/42542447894); that is **PENDING**, do not record it as accepted yet. The source-specific physical pullback/global four-piece `Ḣ¹` and time-positive original full Hartree PDE remainder remain open. Original revised numerator **11/13**.


### 2026-11-09 strict replays and uniform physical-clock shell closure candidate

**Original revised manuscript: 11/13 (84.62%); §2.13 and final Type-II theorem remain OPEN.**

Three original radial-H1 links are now genuinely successful, not merely pending:

- [42542447894](https://github.com/penghongzhong/HBL/actions/runs/42542447894), target `actual_Hartree_matched_radial_H1_density_integrable`, artifact `13642596037`: the genuine matched a.e. derivative has integrable radial \(r^2|\partial_r w|^2\) density.
- [42542644210](https://github.com/penghongzhong/HBL/actions/runs/42542644210), target `actual_Hartree_matched_radial_H1_of_algebraic_slope_bound`, artifact `13642297624`: the actual radial gradient integral is bounded by the *algebraic* weighted slope certificate. This fixes the previous unused-binder strict failure in 42541465634.
- [42542644205](https://github.com/penghongzhong/HBL/actions/runs/42542644205), target `actual_Hartree_true_selected_full_matched_radial_H1_no_left_radius`, artifact `13642522324`: the SAME genuinely selected physical Hartree source, unique real Cramer pair and Fredholm outgoing trace yield the actual normalized three-dimensional Kummer annular H1 bound.

Each original job log explicitly reports transitive axioms `[propext, Classical.choice, Quot.sound]`; each is pinned Lean 4.35.0-rc3 / Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, uses `--trust=0`, `-DwarningAsError=true`, and a target `#check` plus `#print axioms`. Also [42540898273](https://github.com/penghongzhong/HBL/actions/runs/42540898273) strictly succeeded after source lint repair; [42541952006](https://github.com/penghongzhong/HBL/actions/runs/42541952006) strictly succeeded for the original clock integral.

**Strictly certified removal of the shell-clock quantifier gap:** new `ActualHartreeUniformFullShellClockNoBeta.lean` (commit [378bbf2](https://github.com/penghongzhong/HBL/commit/378bbf2cb95cb8a4a7c44b2db6362f4a1e598429)), dedicated strict workflow commit [c0f7550](https://github.com/penghongzhong/HBL/commit/c0f7550a91ba22e640aa7dc9b3d5d7c3124c6efc), [CI 42543500708](https://github.com/penghongzhong/HBL/actions/runs/42543500708). The strictly accepted exact theorem `actual_Hartree_one_orbit_full_shell_uniform_clock_no_beta` fixes cutoff constants *before* the actual PDE orbit, time and radius, and concludes for \(R(s)\le r\le 2R(s)\)
\[
 \left\|\mathcal R[\chi_{R(s)}f](s,r)-\chi_{R(s)}(r)\mathcal R[f](s,r)\right\|
 \le K(M,B,A,J)\,t'(s),\qquad t'(s)=\ell(s)^2,\quad 0<\ell(s)\le1.
\]
No \(\ell(s)\le s^{-\beta}\) assumption or Type-II rate appears. This conclusion **still requires** its stated actual Hartree moment flux and source regularity hypotheses and is only the moving overlap shell, not the complete four-region nonlinear residual. The right-hand coefficient is time-uniform only if \(M,B,A,J\) are themselves uniformly controlled along the true PDE orbit. **Independent original strict CI 42543500708: SUCCESS**, target `actual_Hartree_one_orbit_full_shell_uniform_clock_no_beta`, original evidence artifact `13642179902`. Its job log confirms `lake env lean --trust=0 -DwarningAsError=true`, the exact target `#check` and `#print axioms`, and transitive axioms exactly `[propext, Classical.choice, Quot.sound]` without `sorryAx` or `admit`. This accepts universal constant source-derived rate-free clock domination on the genuine original Hartree overlap shell; it does **not** prove an `s`-power residual order, a complete four-region residual, or the original manuscript theorem.

**Decisive remaining proof gate:** choose a *single time-dependent* compatible true Hartree orbit, derive quantitative modulation/source/endpoint Lipschitz with constants on the whole interval, and prove a genuine strict increment in the original weighted norm for all four regions (not a telescoping identity); then generate and verify the actual finite recursion and dynamically selected Type-II blowup rate. The newly accepted fixed-shell theorem does not move the original 11/13 score.


### 2026-11-09 direct main-theorem dependency audit: actual full-shell integral and nontrivial core-path defect

**Main theorem target kept unchanged:** existence of a genuine radial strong solution of the original energy-critical 3D inverse-square Hartree PDE, bounded critical energy, dynamically selected and unprescribed $\mu_\infty>9/16$ and finite-time single-bubble Type-II blowup. Retained revised 13-slot accounting is **11/13**, regardless of new auxiliary files or jobs. This audit explicitly rules out replacing the missing PDE solution with a conditional terminal criterion.

**New full nonlocal physical-shell spacetime integral (submitted; not yet accepted):**
- Source \`HBL/TypeIIDynamicSelection/ActualHartreeUniformFullShellClockIntegral.lean\`, commit \`ff4c78a3009e74d256d9fcc42b557a414aaa6a1a\`, dedicated workflow \`.github/workflows/hbl-213-uniform-shell-clock-integral.yml\`, commit \`39f8c42c2c3e6d9561bbe93853e948aa3b79072a\`.
- [CI 42546689719](https://github.com/penghongzhong/HBL/actions/runs/42546689719): pending strict audit at submission.
- The new target \`actual_Hartree_one_orbit_uniform_full_shell_clock_integral\` uses the actual complete nonlinear quartic Hartree shell residual along one physical moving radius $R(s)\le r(s)\le2R(s)$, with **one universal cutoff constant triple**. Under the original Hartree moment-flux, true modulation equations, Strauss/regularity inputs and continuity of this literal complex residual along the chosen shell trajectory, it proves
  $$
  \int_{s_0}^{s_1}
  \|\mathcal R[\chi_{R(\sigma)}f](\sigma,r(\sigma))-
      \chi_{R(\sigma)}(r(\sigma))
      \mathcal R[f](\sigma,r(\sigma))\|\,d\sigma
  \le K(M,B,A,J)\,[t(s_1)-t(s_0)] .
  $$
  No independent decay envelope, $s^{-\beta}$ trap, chosen blowup exponent or assumed residual-order increment appears. The **continuity** of the exact residual and the uniform physical bounds are visible inputs, not yet derived globally from the eventual Hartree fixed point. This is an integrated **shell-only** estimate and not the full four-region profile residual. Do not label this Success before job completion.

**Major newly identified logical restriction in the six-atom finite-profile producer:**
- \`ActualHartreeCorrectionResidualAtom.lean\` assumes \`hsame : ∀ s≥1, c1 s = c0 s\` while simultaneously imposing \`c0'(s)=-b(s)c0(s)+m(s)\` and \`c1'(s)=-(b(s)+db(s))c1(s)+m(s)\`.
- On every interior time $s>1$ where the hypotheses apply, the shared value path has the same derivative. Subtraction yields the **necessary identity**
  $$
    db(s)\,c_0(s)=0.
  $$
  Unless $c_0(s)\equiv0$ on the support of the speed correction, a generic nonzero real $\Delta b$ cannot satisfy the old global-equality hypothesis. Accordingly the existing \`actual_Hartree_correction_remainder_realized_atom\` is a **restricted comparison theorem**, not yet a valid generic true-orbit iterative correction producer. The six-atom order-floor theorem does not repair this restriction.
- Required non-circular repair: derive the exact extra physical core-parameter and time-tangent difference generated by $c_1-c_0$, including its genuine nonlocal quartic Hartree interaction, and prove its original weighted norm is higher order from the actual two-channel modulation equations. Alternatively use a single evolving core path with one consistent speed when defining the correction and rederive its principal operator. Neither can be replaced by silently setting $db=0$ or by assuming the extra core defect has the target order.

**Decisive remaining producer chain:** one actual evolving Hartree source / primitive three-Riesz time-velocity majorants and moving Kummer/selected interface derivatives → truly global four-region nonlinear residual with a positive relative order and its two-parameter Lipschitz in the original Fredholm/threshold norm → non-vacuous physical finite correction packets with consistent core/speed ODE → actual weighted backward Hartree orbit and its $\mu_s$ bound → output $\mu_\infty>9/16$ and dynamical blowup rate. All are **OPEN** until their own exact kernel-checked statements are accepted.


### Critical spatial-weight scaling check for the no-beta physical-clock strategy (2026-11-09)

Directly auditing the **already present genuine PDE estimate**
\`ActualHartreeStraussWeightedFullRiesz.lean\` gives, for \(3/2<\sigma<2\),
\[
 \left\|\langle r\rangle^\sigma
  \big(\mathcal N(\chi_R Z_\ell)-\chi_R\mathcal N(Z_\ell)\big)
 \right\|_{L^2(0,\infty)}
 \le C(B,A)\,\langle 2R\rangle^\sigma R^{1/2}
      \ell^{5/2}.
\]
With genuine moving moment radius
\(R=4/(\kappa_{\rm H}\ell\,m_0(z))\), and \emph{only if}
\(m_0(z)\) has uniform positive upper/lower bounds, the right
side scales as
\[
  C(B,A,m_0)\,\ell^{\,2-\sigma}.
\]
At the manuscript Fredholm weight \(\sigma=7/4\) this is
\(C\ell^{1/4}\), **not** \(C\ell^{2}\) or
\(C\ell^{5/2}\). Therefore even the strictly accepted
pointwise universal shell bound \(E_{\rm sh}(s,r)\le K\,t_s(s)\),
\(t_s=\ell^2\), does NOT automatically imply a spacetime
weighted-\(L^2\) norm of full-shell error integrable by the
physical-clock tail.

The algebraic issue is real: the admissible positive scale
\(\ell(s)=1/s\) has \(\int_1^\infty \ell(s)^2\,ds<\infty\),
whereas \(\int_1^\infty\ell(s)^{1/4}\,ds=\infty\).
This is a scalar counterexample to the **proposed implication**,
not a Hartree PDE counterexample. Any proof of the original
\(O(s^{-9/4})\) Fredholm/threshold forcing must use extra PDE-derived
cancellation, a stronger weighted spatial estimate, or a genuinely
deduced scale-decay bootstrap; it cannot be inferred from the
clock-only \(L^\infty_r\) estimate. The currently submitted
time-integrated CI 42547747317 concerns one moving radius
\(r(s)\), not the entire weighted spatial norm.

Keep unchanged the **11/13** original environment count until the
full original PDE norm, real finite correction recurrence and
dynamical rate are constructed.


### Original Hartree nonlinear correction without incompatible core paths: STRICT SUCCESS 42547533614

**Strict original CI** [42547533614](https://github.com/penghongzhong/HBL/actions/runs/42547533614) **SUCCESS** on commit [d7ecbe316](https://github.com/penghongzhong/HBL/commit/d7ecbe3160f04be812501cb1cb7fe9b7e0ada54d); artifact **13644785150**. Source file \`HBL/TypeIIDynamicSelection/ActualHartreeOneGlobalCoreCorrectionNextLayer.lean\` came from commit \`263e8d1b4a4588c81cb5397de85900eb9a836406\`. Decoded original job logs show strict \`lake build\`, \`lake env lean --trust=0 -DwarningAsError=true\`, exact \`#check\` of BOTH theorem types, exact individual \`#print axioms\`, successful parsing of **two** transitive axiom reports:
1. \`actual_Hartree_one_global_core_correction_remainder_exact\`: \`[propext, Classical.choice, Quot.sound]\`;
2. \`actual_Hartree_one_global_core_correction_next_physical_layer\`: \`[propext, Classical.choice.{u}, Quot.sound.{u}]\`.

No \`sorryAx\` nor new axiom; pinned compiler Mathlib as required. On a single global complex background \`U\` and correction \`H\`, define the *literal original nonlocal quartic Hartree PDE* residual
\[
 \mathcal E_{U,H}
 = \mathcal R[U+H;b+\Delta b,\omega+\Delta\omega]
   -\mathcal R[U;b,\omega]-\mathcal P_U(H;\Delta b,\Delta\omega),
\]
where \(\mathcal P_U\) contains the genuine PDE linearization and the
\(\Delta b\,\Lambda U,\Delta\omega\,U\) modulation source, but not the speed
cross on \(H\). Lean proves **exactly**
\[
 \mathcal E_{U,H}
 = i\Delta b\,\Lambda H+\Delta\omega\,H+\mathcal Q_{\rm H}(U,H),
\]
where \(\mathcal Q_{\rm H}\) is the original complete quartic nonlocal Hartree Taylor remainder. Under the theorem's explicit uniform bubble envelope for \(U\), decaying \(H\) and dilation, and true two-speed bound, the derived norm is
\[
 \|\mathcal E_{U,H}(s,r)\|
 \le \Big(C_{\rm speed}(C_{Hd}+C_H)
    +63(M+C_H)^5 C_H^2 {\rm bubble}(r)^5\Big)
      s^{-(\rho+\kappa_{\rm phys})},\quad
 0<\kappa_{\rm phys}\le\rho.
\]
This removes the **global equality** \`c1(s)=c0(s)\` from the nonlinear layer, so the new proof does **not** force \(\Delta b\,c=0\). The principal correction equation, true four-region global field, strong radiation nonlocal feedback, source class and speed norms, two-coordinate parameter Lipschitz and actual finite iteration remain separate **unproved** HBL §2.13 producer obligations.

**Next source-faithful atom candidate:** \`ActualHartreeOneGlobalCoreCorrectionResidualAtom.lean\`, source commit \`4d5d774743cbe7ac78840b1c2690a39f5688edd5\`, strict [CI 42547935578](https://github.com/penghongzhong/HBL/actions/runs/42547935578) under run at this checkpoint. It packages the *same explicit physical residual* into the downstream \`WeightedResidualAtom\`, rather than the globally impossible two-core condition. Do **not** accept before its separate strict CI and exact axiom audit.

The original manuscript remains **11/13 (84.62%)**, neither §2.13 nor final Type-II existence/dynamic rate has been established.


### Genuine moving-shell spacetime integral STRICT SUCCESS 42547747317

Previously failed [CI 42546689719](https://github.com/penghongzhong/HBL/actions/runs/42546689719) was an actual Lean elaboration error at \`ActualHartreeUniformFullShellClockIntegral.lean:168:6\`: \`intervalIntegral.integral_const_mul\` is an equality theorem and was erroneously applied as a three-argument function. No mathematical hypothesis or target statement was changed. Fixed in commit [01c263a](https://github.com/penghongzhong/HBL/commit/01c263a0e855ed2df96586891a518270ccf40f55) by rewriting with \`rw [intervalIntegral.integral_const_mul]\`.

**Replacement strict [CI 42547747317](https://github.com/penghongzhong/HBL/actions/runs/42547747317): SUCCESS**, original evidence **13644346248**, target exact \`#check @HBL.TypeIIDynamicSelection.actual_Hartree_one_orbit_uniform_full_shell_clock_integral\` and \`#print axioms\` accepted. Log explicitly confirms \`lake env lean --trust=0 -DwarningAsError=true\`, \`[propext, Classical.choice, Quot.sound]\`, no \`sorryAx\`. The strict theorem proves an interval-integrated bound on the original full nonlocal quartic Hartree **moving-shell commutator evaluated along a radius trajectory** \`r(s)∈[R(s),2R(s)]\` under the stated original flux/regularity/continuity assumptions, by the actual physical clock increment, without imposing any renormalized scale power trap. It is not a full weighted spatial-in-time source estimate. The explicit scaling countercheck above remains binding.

**New original-residual atom CI repair:** [42547935578](https://github.com/penghongzhong/HBL/actions/runs/42547935578) failed on \`ActualHartreeOneGlobalCoreCorrectionResidualAtom.lean\` unknown identifier \`bubble\`, because the correct original \`HBL.Modulation.AffineTail\` namespace was not opened; this was not a mathematical counterexample. Source repaired in [416022b](https://github.com/penghongzhong/HBL/commit/416022b05dac2f5f7ab0316e3bee2b4de46d19ad). Strict replacement [42548637148](https://github.com/penghongzhong/HBL/actions/runs/42548637148) is pending, do not accept before the original job succeeds and exact axiom report is checked. No formal original environment count increment: **11/13**.



### 2026-11-09 exact original CI re-audit, scope and remaining load-bearing norm gap

- **HEAD verification:** preceding source HEAD `fe5501d72a19bfe306f0d25539685252ebe27634` (2026-11-09 02:02:54 UTC); documentation-only sync is deliberately excluded from the strict theorem numerator. The locked revised 13 environments remain **11/13 (84.62%)**.
- **Actual spectral four-piece full nonlocal Hartree finite PDE telescope**: initial strict [42530158681](https://github.com/penghongzhong/HBL/actions/runs/42530158681) FAILED due to missing upstream `InWeightedL2` symbol in `ActualHartreeSpectralCorrectedFourPieceThreeC1.lean` and a type mismatch, as shown in its original job log. After dependency correction, [42532174421](https://github.com/penghongzhong/HBL/actions/runs/42532174421) SUCCEEDED. Independent renewed strict [42536552509](https://github.com/penghongzhong/HBL/actions/runs/42536552509) SUCCEEDED with original evidence artifact **13639851938**, `lake env lean --trust=0 -DwarningAsError=true`, exact `#check @HBL.TypeIIDynamicSelection.actual_Hartree_finite_spectral_Fredholm_four_piece_full_PDE_telescopes` and `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`. This theorem telescopes exact nonlinear residual differences on successive full corrected backgrounds. It does **not** imply any positive time-order PDE error bound.
- **One global actual-Hartree corrected residual atom**: [42548637148](https://github.com/penghongzhong/HBL/actions/runs/42548637148) is now **SUCCESS** (not pending), source commit `416022b05dac2f5f7ab0316e3bee2b4de46d19ad`, original evidence **13645185877**, exact audited target `HBL.TypeIIDynamicSelection.actual_Hartree_one_global_core_correction_realized_atom`. Original job confirms pinned compiler/dependencies, `--trust=0`, `warningAsError`, exact `#check` and `#print axioms`; transitive axioms **exactly** `[propext, Classical.choice, Quot.sound]`, no `sorryAx` or added axiom. The previous run **42547935578** failed because the original `bubble` namespace was not opened, now repaired. The atom's value is the literal same-global-background quartic nonlocal PDE remainder at a **fixed radial position**; it is conditionally bounded in time by `C s^(-rho-kappa_phys)` from explicit background/correction/speed bounds, with no second incompatible core-parameter path.
- **Decisive non-circularity and norm boundary:** `WeightedResidualAtom ℂ` in `HBL/FiniteProfileResidualLedger.lean` is a **time-weighted scalar** class. Its theorem `actual_Hartree_one_global_core_correction_realized_atom` fixes `r>0` before constructing the atom. Thus it is **not** a theorem of the full spatial norm `‖⟨r⟩^(7/4) E(s,·)‖_(L²(dr)) ≤ C s^(-rho-kappa_phys)`. The scalar uniform bound obtained by replacing `bubble(r)^5` with 1 is not spatially integrable on the half-line. The speed-cross terms require a genuinely integrable radial profile and uniform moving-domain bounds, and the true correction `H` plus its principal equation must be derived from the **same four-piece physical Hartree orbit**. Earlier clock-only weighted scaling `ell^(2-sigma)` at sigma=7/4 gives `ell^(1/4)`, not `ell^2`. Neither a fixed-radius time atom nor the physical-clock shell integral resolves this. This is a **blocking mathematical norm gap**, not a CI elaboration error.
- **Next exact main-chain obligations (no surrogate assumptions):** physical moving-basis Kummer derivative and the uniquely selected four-piece correction actually solving the principal Hartree PDE; genuine spatially weighted full four-region remainder with rate-free integrability or source-derived `s^(-9/4)` and two-threshold-coordinate Lipschitz; finite physical correction recurrence; original dynamical modulation/terminal shooting producing `mu_infty>9/16` and the Type-II law. Only strict closure of the original §2.13 increases the numerator to **12/13**, and only the derived Type-II theorem increases it to **13/13**.


### 2026-11-09: retain the radial spatial profile in the original nonlinear correction (strict replay pending)

A single physical background `U(s,r)`, its correction `H(s,r)`, and the literal original nonlocal quartic PDE yield the exact identity
\[
\mathcal E_{U,H}
=i\,\Delta b\,\Lambda H+\Delta\omega\,H+\mathcal Q_{\mathrm H}(U,H).
\]
The old realized `WeightedResidualAtom` hides the spatial gain by flattening both modulation crosses into a radius-independent constant. The new **source file**
`HBL/TypeIIDynamicSelection/ActualHartreeOneGlobalCoreSpatialRemainderBridge.lean` (latest source commit [ec8efcee](https://github.com/penghongzhong/HBL/commit/ec8efcee88434c0bd91b05ed45d95dd9a5673d5f)) instead retains **actual** radii:
\[
|\mathcal E_{U,H}(s,r)|
\le C_v s^{-\rho}(|\Lambda H(s,r)|+|H(s,r)|)
+63(M+C_Hs^{-\rho})^5 C_H^2s^{-2\rho}(1+r^2)^{-5/2}.
\]
This statement needs the *visible* pointwise original-field bubble assumptions, speed control, regularity and measurability, but does **not** assume a radius-independent norm for \(\Lambda H\) or a residual gain. Initial [CI 42551656354](https://github.com/penghongzhong/HBL/actions/runs/42551656354) failed at the two complex-norm simplifications (its raw job reported \(\|db\|=|db|\) not discharged). They were corrected in commit `ec8efcee`; replacement [strict CI 42552019761](https://github.com/penghongzhong/HBL/actions/runs/42552019761) is **SUCCESS**. Its original job 128949475926 reports the literal `lake env lean --trust=0 -DwarningAsError=true` build, zero-byte `strict.log`, exact target `#check @HBL.TypeIIDynamicSelection.actual_Hartree_one_global_core_spatial_remainder_bound`, exact `#print axioms`, and the accepted dependency list **[propext, Classical.choice, Quot.sound]**, with no `sorryAx` or `admit`. Original archived evidence: [artifact 13645594881](https://github.com/penghongzhong/HBL/actions/runs/42552019761/artifacts/13645594881). Lean 4.35.0-rc3, Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`. This is one **new verified auxiliary theorem**, not a revised original §2.13 proof; the accepted original-environment count stays 11/13.

**Exact quantitative remaining norm gate** (mathematical consequence, NOT yet a Lean-accepted full source theorem): with \(w(r)=(1+r^2)^{7/8}\), the Fredholm conjugated source is \(r\mathcal E\). If the actual field's two speed-cross norms are finite, then
\[
\|wr\mathcal E(s,\cdot)\|_{L^2(0,\infty)}
\le C_vs^{-\rho}\bigl(\|wr\Lambda H_s\|_2+\|wrH_s\|_2\bigr)
+63(M+C_Hs^{-\rho})^5C_H^2s^{-2\rho}\,C_*,
\]
\[
C_*^2=\int_0^\infty r^2(1+r^2)^{-13/4}\,dr
=\tfrac12\mathrm B(\tfrac32,\tfrac74)<\infty.
\]
The speed-cross norms are **not** derived by the fixed-radius `WeightedResidualAtom`. Indeed the generic bubble majorant \(|H|\lesssim (1+r^2)^{-1/2}\) alone fails to place \(rH\) in this globally weighted \(L^2\). The **actual mixed regional source space** remains the intended route: weighted conjugated inner source and unweighted exterior source (as in `ActualHartreeTwoWeightPhysicalSourceClosure.lean`), with true moving-shell support, physical speeds, Green/repair fields, and their parameter differences. Do not replace this with a fictitious global norm assumption, and do not assert the missing \(s^{-9/4}\) rate. Original revised manuscript tally stays **11/13**; §2.13 and Type-II main theorem remain open.


### 2026-11-09: quantified moving-shell radial-conjugation loss — cannot convert the clock bound by support alone

The existing actual moving-shell PDE clock estimate yields a **pointwise** residual on \(R(s)\le r\le2R(s)\) bounded by \(C\ell(s)^{5/2}\) before weakening to \(C t_s=C\ell(s)^2\); the actual radial-conjugated inner Fredholm forcing is \(rE\), not \(E\). Applying the original shell geometry of \`ActualHartreeShellWeightedNorm.lean\` to a shell residual of this amplitude gives, for \(R\ge1\),
\[
\|\langle r\rangle^{7/4}r\,\mathbf 1_{(R,2R)}E\|_{L^2(dr)}
\le20\,C\,R^{13/4}\ell^{5/2}.
\]
Even if the *actual moment radius* has the independently known upper window \(R\le Q/\ell\) and \(0<\ell\le1\), this crude implication is only
\[
\|\langle r\rangle^{7/4}r\,\mathbf 1_{(R,2R)}E\|_2
\le20\,C\,Q^{13/4}\ell^{-3/4},
\]
**not** a vanishing positive gain. The estimate does not say the actual shell norm diverges: it proves only that a radius-independent pointwise clock bound and shell support alone cannot close the required Fredholm source budget. One needs stronger genuine spatial decay/cancellation, region-specific norms or actual PDE control of the remaining moving modes. This radius power is not an optional bookkeeping factor. No increase to 12/13.


### 2026-11-09 original conjugated shell norm: actual nonlinear residual and explicit radius loss

The exact same-global-background original quartic Hartree residual is now
inserted into the genuine radial (q=rH) source, rather than reusing a
scalar-in-time `WeightedResidualAtom`. New Lean module
`ActualHartreeOneGlobalCoreConjugatedShellWeighted.lean` at commit
[`3223bb8`](https://github.com/penghongzhong/HBL/commit/3223bb8ba464ead0f22636e2821f6685c898f094)
and strict workflow at
[`e707b646`](https://github.com/penghongzhong/HBL/commit/e707b64641473deebe0e51832c414278fda7b0b1)
have independent [CI 42553324852](https://github.com/penghongzhong/HBL/actions/runs/42553324852).
**Initial CI 42553324852 FAILED** solely on the Lean addition-order elaboration of a proved scalar coefficient bound at line 115 (original job log). Source was repaired at [903b870](https://github.com/penghongzhong/HBL/commit/903b870ee09088c28b24fa1b90b9cdfc2f0d4d67) with direct `add_le_add (le_refl _) hh2`; **replacement [CI 42554311787](https://github.com/penghongzhong/HBL/actions/runs/42554311787) is strictly SUCCESS**; original job 128956509687 confirms `--trust=0`, `warningAsError`, exact `#check` and `#print axioms`, with exactly `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

For true (E_{U,H}:=\mathcal R[U+H]-\mathcal R[U]-\mathcal P_U(H)),
(s\ge1), (R\ge1), under the same-orbit regularity, speed and field
bounds explicitly present in the theorem, the proposed verified target is
[
 \mathbf1_{(R,2R)}r|E_{U,H}(s,r)|\in L^{2,7/4}(dr),\qquad
 \|\mathbf1_{(R,2R)}r|E_{U,H}(s,r)|\|_{L^{2,7/4}}
 \le 20R^{13/4}C_0s^{-(\rho+\kappa_{\rm phys})},
]
where
(C_0=C_{\rm speed}(C_{\Lambda H}+C_H)+63(M+C_H)^5C_H^2).
This explicitly preserves the original conjugation factor (r), weight
(r^{7/4}) and shell-volume factor (R^{1/2}). A blanket
(O(s^{-\rho-\kappa})) pointwise residual does **not** yield the original
(O(s^{-9/4})) four-region norm without further spatial decay.
If one later derives (R(s)\lesssim s^{1/2}) from actual modulation, the
coarse estimate is at most (O(s^{-(\rho+\kappa-13/8)})); achieving the
original order by *this coarse bound* requires
(\rho+\kappa\ge31/8). That is not an assumed law.

**Additional non-circularity audit:** the historical
`ActualHartreeKummerTailTimeGain.lean` and
`ActualKummerPhysicalRepairTimeGain.lean` turn
(L^{-3/8}=\ell^{3/128}) into an (s)-power by the explicit
bootstrap `htrap : ell ≤ s ^ (-beta)`. This remains a conditional
source of time order, not a PDE-derived rate and not an allowed
final-threshold input. The physical clock/shell route bypasses
`htrap` for selected overlap-shell terms only; global Kummer repair,
selected-speed derivative and recursion still need a rate-free source
of gain. **Original acceptance: 11/13.**


### Kinematic counterexample to obtaining a power bootstrap from the physical clock alone

Even the correct modulation kinematics and a finite physical terminal time
**do not** force \(\ell(s)\lesssim s^{-\beta}\) for any
\(\beta>1/2\). On \(s\ge1\), take the smooth positive scale
\[
 \ell(s)=\frac{s^{-1/2}}{\log(s+e)},\qquad
 b(s)=\frac{1}{2s}+\frac{1}{(s+e)\log(s+e)},\qquad
 t(s)=t(1)+\int_1^s\ell(\tau)^2\,d\tau.
\]
Then
\[
 \ell_s=-b\ell,\quad t_s=\ell^2,\quad b>0,\qquad
 \int_1^\infty \ell(s)^2\,ds
  =\int_1^\infty\frac{ds}{s\log^2(s+e)}<\infty,
\]
yet for **every** \(\beta>1/2\),
\(s^\beta\ell(s)=s^{\beta-1/2}/\log(s+e)\to\infty\).
This is an exact classical counterexample at the **kinematic** level,
not an assertion that this trajectory solves the Hartree PDE. Therefore
the \`htrap\` powers in the old Kummer/finite profile gains require a
genuine **additional modulation equation derived from Hartree**, not
just \(\ell_s=-b\ell\) and \(t_s=\ell^2\).
A sufficient non-circular target is a PDE-produced differential bound
\(b(s)\ge(1/2+\delta)/s\), \(\delta>0\), which integrates to
\(\ell(s)\le C s^{-1/2-\delta}\).
That bound is **unproved for the actual four-region orbit**.
This explicitly delineates where a dynamical rate must enter the
proof *before* the original §2.13 power closure. No new original environment.


### 2026-11-09 strict replays and full-source weighted shell norm — original evidence, no original count increment

The earlier requested CI set is now reconciled with **later** strict evidence,
not naively treated as permanently failed: `42531450638` (zero-left
regularized Volterra radial slope, artifact `13638185198`), `42531500587`
(matched zero-left spectral weighted C¹, artifact `13637228884`),
and `42531018076` (genuine selected full original Green, artifact
`13637702928`) each reported **SUCCESS**. The initial four-piece
three-C¹ CIs `42531033761/768` and the initial selected-source
joint C¹/quadratic CIs `42531467165/166` had an actual upstream
`HasDerivAt`-type mismatch (and one `dsimp` no-progress error).
The later corrected **SUCCESS** runs are
`42532174427` (physical spectral four-piece three C¹),
`42532174429` (same uniquely real-selected source and three C¹),
`42532363535` (true selected spectral quadratic and three C¹),
and the fully joint selected physical source/no-left-loss radial H¹
and spectral three-C¹ certificate `42539718869`.
The last run's original audit prints exactly
`[propext, Classical.choice, Quot.sound]`, artifact `13641491217`.
All of these are **auxiliary** strict proofs, not the original §2.13 PDE theorem.

The initially failing finite-field nonlinear telescope
`42530158681` had already been repaired and fully strictly
accepted in `42532174421`, with renewed original strict
`42536552509` SUCCESS, original evidence artifact `13639851938`.
This is an **exact** telescope of the untruncated original nonlinear
PDE residual on a sum of spectral four-piece fields, not a claim
that the increments are positive time order. A further current-HEAD
replay was triggered from source commit
[`2f83bf26e`](https://github.com/penghongzhong/HBL/commit/2f83bf26eecf4d8d8eb3c67c7da3114507aff3ae),
[CI `42553800224`](https://github.com/penghongzhong/HBL/actions/runs/42553800224)
has now **strictly SUCCEEDED**, original job `128954948052`,
artifact **13646732923**. The workflow rebuilt the actual finite
spectral-corrected four-zone field under pinned Lean 4.35.0-rc3 and
Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`,
ran exact `#check` and `#print axioms` under
`--trust=0 -DwarningAsError=true`, and the original job explicitly
accepted only `[propext, Classical.choice, Quot.sound]`.
No `sorryAx` or additional axiom. This is a true **auxiliary
nonlinear PDE identity**, not a residual time-gain estimate.

The new `ActualHartreeOneGlobalCoreConjugatedShellWeighted.lean`
treats the *literal* same-background Hartree correction residual in
the original conjugated norm, exposing the shell factor
\(R^{13/4}\). Initial [CI `42553324852`](https://github.com/penghongzhong/HBL/actions/runs/42553324852)
failed on an **elementary Lean coefficient reassociation** at line 115:
`add_le_add_left` was applied to a bound ending in
`(...)*1` rather than the simplified coefficient. The mathematical
claim and all premises were preserved; fix commit
[`c830face`](https://github.com/penghongzhong/HBL/commit/c830face510691682b1709866fc1f5edb08018f0)
rewrites `hh2` using `mul_one` before adding the nonnegative
coefficient. Replacement [strict CI `42554265089`](https://github.com/penghongzhong/HBL/actions/runs/42554265089)
is **pending** at this ledger checkpoint; do not add it to accepted
proofs until job logs, exact `#check`, `#print axioms`, and
`--trust=0` are confirmed. A conditional shell norm without the
global four-region correction or actual selected-speed derivative is
still **not** an accepted original section.

Exact original-environment ledger: **11/13 (84.62%)**, §2.13 open,
final dynamically obtained Type-II theorem open.


### Potential shortest terminal link: rate-free qualitative Type-II criterion (analytic, NOT Lean acceptance)

If a **genuine PDE-generated** concentration scale satisfies
\[
 \ell_s=-b\ell,\qquad t_s=\ell^2,\qquad
 T=\lim_{s\to\infty}t(s)<\infty,\qquad \ell(s)>0,
\]
then for every \(s\), writing \(B_s=\sup_{u\ge s}b(u)\in(0,\infty)\),
\(\ell(u)\ge\ell(s)e^{-B_s(u-s)}\) for \(u\ge s\). Consequently
\[
 T-t(s)=\int_s^\infty\ell(u)^2\,du
 \ge \frac{\ell(s)^2}{2B_s},
 \qquad
 \frac{\ell(s)^2}{T-t(s)}\le2B_s.
\]
Thus a separately derived \(b(s)\to0\) and finite terminal physical
time imply the **qualitative Type-II scale**
\(\ell(s)=o(\sqrt{T-t(s)})\), without any prescribed \(s^{-\beta}\)
power. This is proposed as a shorter final step, **not a replacement**
for an original theorem demanding a specific numerical explosion
exponent and **not** a claimed Lean theorem.
Neither \(T<\infty\) nor \(b(s)\to0\) is currently proven for the
real four-domain Hartree profile, and those are genuine PDE obligations.


### Candidate weak moving-interface shortcut (not yet a Lean theorem)

To shorten the actual time-dependent four-piece PDE chain, formulate
the nonlinear residual first in the weak/spatial-a.e. sense. For a
moving boundary \(r=R(s)\) and fields \(u_-,u_+\) on either side,
the distributional interface terms are respectively proportional to
\(R_s[u]\) in \(\partial_s u\), \([u]\) in \(\partial_r u\),
and \([\partial_r u]\) in \(\partial_r^2u\), where
\([u]=u_+-u_-\). The already **fixed-slice** accepted three-\(C^1\)
matching removes the spatial jump coefficients and also the time
distributional delta, once those matches hold along the same moving
physical interface for each \(s\). Therefore the original \(L^2\)
residual can in principle be reduced to four **bulk** PDE residuals
a.e., without demanding pointwise second derivatives *at* each join.
This still requires a rigorous moving Sobolev-gluing theorem,
measurable/time-regular bulk fields, and a genuine PDE-source estimate
for all four domains and the selected modulations. Nothing is counted
as accepted on the basis of this proposed route.


### 2026-11-09 unshifted original-spectral strict PDE and backward-shell source

**New strict Success** [42562774111](https://github.com/penghongzhong/HBL/actions/runs/42562774111), source [22799826](https://github.com/penghongzhong/HBL/commit/2279982605566d97f5a835edf0531f7a9865c070), original job 128982599861, evidence artifact 13650098975. Two exact audited theorem types in ActualHartreeMatchedSpectralOriginalPDEMismatch.lean establish, for the original normalized Kummer Green and its genuine spectral correction,
\[
 \mathcal L_K(u_0-u_1)=F-\delta u_0,\qquad
 \mathcal L_K^{(a)}[(u_0-u_1)(\cdot/a)]
    =a^{-2}[F(\cdot/a)-\delta u_0(\cdot/a)].
\]
Original CI contains Lean 4.35.0-rc3, pinned Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, trust=0, warningAsError, exact #check and #print axioms for BOTH targets, zero-byte strict.log, and precisely the allowed three transitive axiom families, with no sorryAx or admit. This formally proves an exact ORIGINAL-PDE source, not the positive-time §2.13 residual.

On the actual *backward* overlap [R,2R]=[L/2,L], the original Fredholm shell theorem produces
\[
 A_R=(C_{\rm eq}R^{-4}+C_Ka^{-2})N_F,\qquad
 \|u-v_0\|\le8R^2A_R,\qquad \|u\|\le C_{\rm val}N_F.
\]
Thus the original matched Green field obeys
\(\|v_0\|\le D_R:=C_{\rm val}N_F+8R^2A_R\)
**without an independent value envelope** and without invalidly extending the right-annulus Green estimate backwards. Candidate ActualHartreeBackwardMatchedValueGain.lean has [CI 42563548889](https://github.com/penghongzhong/HBL/actions/runs/42563548889). The same-physical-source Hartree plateau cancellation, composed with the first strict original-PDE theorem, is in ActualHartreePlateauSpectralOriginalSourceCancel.lean, [CI 42563426525](https://github.com/penghongzhong/HBL/actions/runs/42563426525).

Candidate ActualHartreeBackwardSpectralFirstOrderShellGain.lean, source [e2623e](https://github.com/penghongzhong/HBL/commit/e2623e76775d60032da9ad714ccee20375e36bc5), [CI 42563980436](https://github.com/penghongzhong/HBL/actions/runs/42563980436), bounds the LITERAL original spectral source via the honest shell geometry
\[
 \|\mathbf1_{(R,2R)}r\,a^{-2}\delta v_0\|_{L^{2,7/4}}
 \le20R^{13/4}a^{-2}|\delta|D_R
 \le20R^{-3/4}|\delta|D_R,\quad a\ge(2R)^3.
\]
These latter three runs are PENDING at this checkpoint, not credited without original Success and exact axiom logs. This is an ell-power shell gain, NOT an s-power or global four-domain Hartree nonlinear residual, parameter Lipschitz, actual finite recursion, or dynamically deduced Type-II rate. **Original acceptance remains 11/13**.


### Operator-selection caution for reference versus moving PDE

An exact Lean theorem for the unshifted reference Kummer operator
does NOT prove that the actual moving-parameter Hartree PDE uses
the same operator. For the real matched spectral construction
\(u_1=G_{K_0}[\delta u_0]\), \(w_\delta=u_0-u_1\), both exact formulas hold:
\[
 \mathcal L_{K_0}w_\delta-F_{\rm adj}=-\delta u_0,\qquad
 (\mathcal L_{K_0}+\delta)w_\delta-F_{\rm adj}=-\delta u_1 .
\]
The first was independently strict-verified in CI 42562774111;
the second is an already checked exact shifted spectral identity.
If the coefficient displacement is actually
\(\delta(s)=q_0(\mu(s),\theta(s))-q_0(\mu_0,\theta_0)\),
the current frozen Kummer operator is \(\mathcal L_{K_0}+\delta(s)\)
and the correct *moving-coefficient spatial* defect is quadratic,
not the reference first-order defect. Thus the first-order backward-shell
bound is a mathematically valid reference-operator source estimate, but
it may be unnecessary for the *true* moving-parameter source.
**The operator used by the actual renormalized 3D Hartree PDE must be
identified exactly** and its moving time transport, basis and
nonlocal feedback retained before choosing either residual estimate.
Do not silently switch operators or assume the spectral mismatch
cannot cancel. This is a decisive remaining main-chain gate, with no
new original-paper acceptance; score remains 11/13.


### 2026-11-09 actual moving spectral plateau and backward inverse-Volterra proof

**Current original revised theorem count 11/13, no credit for auxiliary modules.** Strict GitHub Actions [42565184656](https://github.com/penghongzhong/HBL/actions/runs/42565184656) succeeded on source 88b87b5c, original job 128990057404, artifact 13651342799, exact declaration
HBL.TypeIIDynamicSelection.actual_Hartree_plateau_current_moving_spectrum_exact_quadratic_source.
The same genuine quartic nonlocal Hartree plateau source and both physical real speed channels yield, with
\(\delta=\mathrm{frozenZeroCoeff}(\mu,\theta)-\mathrm{frozenZeroCoeff}(\mu_0,\theta_0)\),
\(u_1=G_{K_0}[\delta u_0;0,0]\), \(v_\delta=(u_0-u_1)(\cdot/a)\),
\[
 \mathcal L_{\mu,\theta}^{(a)}v_\delta+\mathcal S_{\mathrm{inner}}
       =-a^{-2}\delta u_1(\cdot/a)
       \quad (0<y\le L).
\]
The fixed-reference first-order source \(-a^{-2}\delta u_0\) is exactly canceled by the actual changed zero-order Kummer coefficient; the remaining *spatial* error is genuinely quadratic in \(\delta\), conditional on source-derived Volterra bounds. This is not the full Hartree PDE in time. The original run contains Lean 4.35.0-rc3 / Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, --trust=0, -DwarningAsError=true, exact #check and #print axioms; only [propext, Classical.choice, Quot.sound].

**Independent strict SUCCESS** [42565447419](https://github.com/penghongzhong/HBL/actions/runs/42565447419), original job 128990847961, evidence 13651526711, exact declaration
HBL.TypeIIDynamicSelection.actual_Hartree_backward_spectral_first_order_shell_source_gain.
This bounds the genuine *reference* \(-a^{-2}\delta u_0\) shell source in the original conjugated weighted norm by \(20R^{-3/4}|\delta|D_R\) for \(a\ge(2R)^3\). The actual matched physical Green field on the **backward** physical interval \([R,2R]\) is bounded from the two original Fredholm sources (verified [42564376709](https://github.com/penghongzhong/HBL/actions/runs/42564376709), artifact 13650812421), not an independent envelope. Exact trust-zero, warnings-as-errors, and three-axiom audit succeeded. It is **not** yet the moving-coefficient quadratic \(-\delta u_1\) estimate.

**Pending true backward zero-jet Volterra**: source [533d8ef](https://github.com/penghongzhong/HBL/commit/533d8ef616ac9a075f297d631848bf46338cfb1e), strict [CI 42566011025](https://github.com/penghongzhong/HBL/actions/runs/42566011025). Unlike right-annulus estimates, the source is evaluated at normalized \(r\in[r_0/2,r_0]\), **left of its zero-Cauchy-jet anchor** \(r_0=L/a\). The strict target bounds \(G_{K_0}[F;0,0]\) there by \(2G^2M\), from actual reversed Wronskian integrals and \( |F(r)|\le M/r\). For the same physical \(u_0\) and \(F=\delta u_0\), the matched backward value producer suggests \(M=r_0|\delta|D_R\). This would yield a genuinely quadratic spatial source with no inverse moving-radius loss but is **not strict accepted** until its job succeeds. All other four-region, nonlinear time/moving-boundary, modulation-Lipschitz, finite recursion and dynamic Type-II rate obligations remain open.


### 2026-11-09 backward quadratic matched-source CI 42566992080 and exact scale budget (strict pending)

The actual new producer HBL.TypeIIDynamicSelection.actual_Hartree_matched_backward_quadratic_spectral_source was committed in [2387705d](https://github.com/penghongzhong/HBL/commit/2387705d6e5714c8990931da640030a714270359) and given an independent pinned strict [CI 42566992080](https://github.com/penghongzhong/HBL/actions/runs/42566992080). **Not accepted unless full job success and exact single-target axiom audit are confirmed.** Its source calls the original two-channel Fredholm matched backward value theorem and the newly attempted genuine reverse-integral Volterra theorem for the SAME \(u_0\). The true backward original source coherence and its regularity/integrability are visible inputs; it is not a proof of the four-region time residual or unique-speed construction by itself.

Writing \(L=2R\), \(r_0=L/a\), and \(D_R=C_{\rm val}N_F+8R^2\mathcal A_{\rm shell}\), the intended bound follows from the actual source \(q=\delta u_0\), which obeys \(|q(x)|\le r_0|\delta|D_R/x\) on the correctly oriented normalized interval \([r_0/2,r_0]\). The genuine Cramer zero-left inverse would yield
\[
 |u_1(x)|\le2G^2r_0|\delta|D_R,\qquad
 |a^{-2}\delta u_1(y/a)|
     \le 2G^2La^{-3}|\delta|^2D_R
     \quad (R\le y\le2R).
\]
Applying the *original radial-conjugated* shell geometry to the measurable physical residual:
\[
 \|\mathbf1_{(R,2R)}y\,a^{-2}\delta u_1(y/a)\|_{L^{2,7/4}(dy)}
 \le40G^2 LR^{13/4}a^{-3}|\delta|^2D_R.
\]
The genuine established physical separation \(a\ge L^3\) would give the purely **spatial** improvement
\[
 40 LR^{13/4}a^{-3}
 \le(5/32)R^{-19/4}
 = (5/32)\,2^{19/4}\ell^{19/64}
 \quad\text{if }L=2R=\ell^{-1/16}.
\]
**This last norm inequality is still an analytical consequence, not a separate Lean-accepted theorem**: derive residual measurability, identify the same spectrally selected \(u_1\) and its legitimate physical source, and close the pending reverse-Volterra CI first. The 11/13 original statement tally is unchanged. Independently accepted actual-source/variable-coefficient cancellation: [42565184656](https://github.com/penghongzhong/HBL/actions/runs/42565184656) (artifact 13651342799); independent full physical moving coefficient equality: [42566073115](https://github.com/penghongzhong/HBL/actions/runs/42566073115) (artifact 13651906616). Neither assigns an \(s^{-9/4}\) bound.
\n\n## 2026-11-09 precise original §2.13 acceptance gate and targeted reversal of the radius-loss argument\n\n- **The original retained 13-environment §2.13 (label `thm:finite-profile-stage3`) is strictly stronger than a frozen-order shell estimate or the newer `LockedSingleOrbitBackward.lean` conditional fixed-point theorem.** The reconciled manuscript actually states: fix `M>4`, `ell_lr>=0`, choose `N>M+3+ell_lr`; construct from the original Hartree PDE one finite physical profile `V_N[h;g]` such that `F_PDE(V_N)=P_N zeta_s+E_N`, `||E_N||_{Y_(M+1+ell_lr)} <= C s0^(M+1+ell_lr-N)`, `D_zeta Theta_N=I_2+o(1)`, and the full Hessian decomposition `L_N=L_0+K_sl+R_int`, including time-derivative integrability, parameter Lipschitz and center/radiation norms. This cannot be credited by a bare `s^(-9/4)` source estimate or by numerical finite termination. The 9/4 backward fixed-point code is an alternative downstream proof route only **after its actual forcing and all profile-to-energy matching are constructed**.\n\n- **New strict source-specific closure (not original count):** [CI 42567116515](https://github.com/penghongzhong/HBL/actions/runs/42567116515), source `fc7e87b`, original job `128995924948`, artifact `13652276776`, strictly verifies BOTH `actual_Hartree_zero_left_original_Green_backward_identity` and `actual_Hartree_zero_left_original_Green_backward_inverse_linear_bound`. The exact reverse Green-Wronskian integral bounds apply on the physically required normalized backward interval `[r0/2,r0]`, with no fictitious extension from the forward interval. Strict audit `--trust=0`, warnings as errors, exactly `propext, Classical.choice, Quot.sound` (universe instantiations permitted).\n\n- **New strict composition (not original count):** [CI 42566992080](https://github.com/penghongzhong/HBL/actions/runs/42566992080), source `2387705d`, original job `128995543355`, artifact `13652650582`. Exact audited `actual_Hartree_matched_backward_quadratic_spectral_source` begins from the original matched two-channel Fredholm field, uses the *same* source `q=delta*u0`, the true zero-Cauchy Green correction `u1=G_K0[q;0,0]` and the reverse interval to prove\n\n  `|a^(-2) delta u1(y/a)| <= a^(-2)|delta| * (2 G^2 ( (2R/a)|delta| D_R ))`, for `R<=y<=2R`. The original log explicitly shows `--trust=0`, `-DwarningAsError=true`, exact target `#check` and `#print axioms`, and only the three allowed axioms. This closes a material source-specific **spatial quadratic** gap, not §2.13.\n\n- **Immediate original radial-conjugated source norm:** New module `ActualHartreeMatchedBackwardQuadraticSpectralWeighted.lean`, source [df93c58b](https://github.com/penghongzhong/HBL/commit/df93c58b7e1caf00415a2e170aa04e77482a3c8d), workflow [4a8642fd](https://github.com/penghongzhong/HBL/commit/4a8642fdbf4eebb760cfb964479a035425d6159f), strict [CI 42568496790](https://github.com/penghongzhong/HBL/actions/runs/42568496790) **SUCCESS** (job `129000199272`, evidence artifact `13652482181`): exact audited `actual_Hartree_matched_backward_quadratic_spectral_source_weighted`, pinned Lean 4.35.0-rc3 / Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, `--trust=0 -DwarningAsError=true`, exact target `#check`, `#print axioms`, no `sorryAx` and precisely `[propext, Classical.choice, Quot.sound]`. It composes the *actual same-source quadratic Green* inequality with the original `InWeightedL2 (7/4)` shell norm, retaining `R^(13/4)`, the physical `a^(-2)` and original field measurability premise. The separately derived scale reduction under `a>= (2R)^3` is `(5/32) G^2 R^(-19/4)|delta|^2 D_R` (analytical implication; do not mark it independently Lean-accepted until a formal target checks it).\n\n- **One viable meaningful shortening** of the manuscript statement is to construct a **single fixed high order `N0>M+3+ell_lr`** for one physical terminal radiation, if downstream energy/gluing and actual selected-rate proof are explicitly reverified for that `N0`. Do not replace it with an arbitrary empty packet list, a `hstep` hypothesis, a mere `mainJet=id`, or only `s^(-9/4)` with no full physical profile. **The currently proved finite recursion remains conditional on `hstep` and labels, not a producer of `V_N`.**\n\n**Strict original manuscript count still 11/13**. To move to 12/13 the missing source-to-profile producer must derive from the *actual four-zone nonlocal Hartree PDE* at least one positive full weighted residual-order step including real moving-time/endpoint and Kummer basis/selected-speed derivatives and parameter Lipschitz; finite continuation must reach the fixed sufficient `N0` and provide its actual Hessian terms. Only then may original §2.13 be accepted. The final dynamically selected Type-II orbit/rate remains the 13th environment.\n

### 2026-11-09 quantitative spectral-shell time-order deficit at admissible beta

This is a **conditional exponent audit** showing why merely piling up the
new quadratic shell lemmas cannot close the original high-order §2.13.

For the physical kinematic choice \(A=4\mu_\infty\), the locked formula in
HBL/KinematicSliceNormalizationBridge.lean is
\(\beta=(A+1)/(2A)=1/2+1/(8\mu_\infty)\). The original target
restricts \(\mu_\infty>9/16\), hence
\[
  \frac12<\beta<\frac{13}{18}.
\]
Under the *hypothetical PDE-produced* terminal parameter speed
\(|\delta(s)|\lesssim s^{-(2\beta-1)}\) and an optimistic matched
Fredholm source budget \(D_R(s)\lesssim\ell(s)^{1/8}\) with
\(\ell(s)\lesssim s^{-\beta}\), the newly obtained spatial bound
\[
 \|r\,a^{-2}\delta u_1\|_{L^{2,7/4}(R,2R)}
 \lesssim \ell^{19/64}|\delta|^2 D_R
\]
yields **only the generic** time exponent
\[
  \rho_{\rm single}=
  2(2\beta-1)+\frac{27\beta}{64}
  =\frac{283\beta}{64}-2
  <\frac{1375}{1152}\approx1.194<\frac94.
\]
The numerical bound is an *upper bound on the order supplied by these
specific generic assumptions*, NOT a lower bound on the true residual;
additional cancellation or stronger physical estimates may improve it.
If \(D_R\) decays more slowly, the guaranteed order is even weaker.
Thus a single frozen spectral correction, even with exact quadratic
cancellation, cannot certify the **required \(s^{-9/4}\)** from these
available generic rate inputs, let alone the original arbitrary fixed
\(N>M+3+\ell_{\rm lr}\). The only honest routes are genuine
higher-order physical recursion with verified source classification,
or a separately justified reformulation of the final shooting/energy
argument. Do NOT multiply the same shell gain repeatedly without
constructing actual new physical PDE corrections.

The exact Kummer quadratic source and backwards Volterra source are
strictly verified; as of this audit the full time-dependent actual
profile, feedback, parameter/Lipschitz estimates and generated-term
recursion remain absent. Revised original count still **11/13**.


## 2026-11-09 new original four-piece/PDE and genuine weighted-source verification checkpoint

The latest branch has strict **Success** for the formerly failing spectral finite PDE telescope: [42648496792](https://github.com/penghongzhong/HBL/actions/runs/42648496792), original job `129268151514`, artifact `13688728524`. Exact target: `HBL.TypeIIDynamicSelection.actual_Hartree_finite_spectral_Fredholm_four_piece_full_PDE_telescopes`; the original CI log includes `--trust=0`, `-DwarningAsError=true`, precise `#check` and `#print axioms`, and prints exactly `[propext, Classical.choice, Quot.sound]`. This eliminates the earlier broken upstream dependency from run 42530158681 **without** mistaking the telescoping identity for a positive-order residual bound.

The actual corrected three-C1 four-piece source is independently successful in [42648994008](https://github.com/penghongzhong/HBL/actions/runs/42648994008). Its same-physical-source selected spectral quadratic companion is successful in [42650515961](https://github.com/penghongzhong/HBL/actions/runs/42650515961) and the spectral original PDE plateau cancellation in [42650515956](https://github.com/penghongzhong/HBL/actions/runs/42650515956). The fifth-power bound for one genuine two-scale quartic density Riesz-times-cubic atom is successful in [42649080513](https://github.com/penghongzhong/HBL/actions/runs/42649080513).

For the *one* genuine nonlinear atom `F(r)=I_2[\mathcal D_{4,\ge 2}(U,H)](r)\,|U(r)|^2U(r)`, put
`P=((6M^2+4Me+e^2)e^2)C_R` and `K=2(D^2+E^2)`. The proved fifth-weight square majorant `(1+r)^5||F(r)||^2\le P^2 K^3` implies the mathematically exact original half-line norm estimate

`\int_0^\infty (1+r^2)^{7/4}||F(r)||^2\,dr \le P^2K^3\int_0^\infty(1+r)^{-3/2}\,dr = 2P^2K^3`.

The target Lean file `ActualHartreeTrueQuadraticRieszCubicWeightedL2.lean` states this native `MemLp 2` estimate on the actual nonlocal source and explicitly **assumes** `||H(r)||\le e\,bubble(r)`; this decay is not independently constructed from the physical PDE. The first strict run [42649085863](https://github.com/penghongzhong/HBL/actions/runs/42649085863) failed on nat/real power coercions. A second strict run [42650866787](https://github.com/penghongzhong/HBL/actions/runs/42650866787) failed at lines 68 and 87 on explicit `^ (2:ℝ)` versus `^ (2:ℕ)`, and `^ (5:ℝ)` versus `^ (5:ℕ)`. Source commit [4dda33f](https://github.com/penghongzhong/HBL/commit/4dda33f5527a16c8655d422cad5109167fbe8c0a) repairs precisely these two failures with `Real.rpow_natCast`; strict [42652808504](https://github.com/penghongzhong/HBL/actions/runs/42652808504) was **running at this checkpoint**. No acceptance is claimed until its actual conclusion and exact axioms are checked.

**Formal revised-paper count: 11/13.** Genuine time-differentiated moving Kummer basis, endpoints and selected speed, the other quartic Taylor atoms, full four-region nonlocal remainder and parameter Lipschitz, and physical fixed high-order profile recursion/Hessian and dynamically selected Type-II rate are still missing. The one-atom norm and the finite telescoping identity must not be promoted to §2.13.
