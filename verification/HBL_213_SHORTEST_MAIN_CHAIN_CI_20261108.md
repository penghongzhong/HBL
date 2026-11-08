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
