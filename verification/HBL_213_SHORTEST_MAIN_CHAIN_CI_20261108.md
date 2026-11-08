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
