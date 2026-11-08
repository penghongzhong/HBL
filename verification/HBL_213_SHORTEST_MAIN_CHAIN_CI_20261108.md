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

## New source-to-weighted-correction integration: strict CI pending

- `ActualHartreeOriginalSelectedSpectralC1Joint.lean` combines the
  **same real selected physical Hartree source** with the joint source-driven
  first-order C¹ and second-order Kummer residual bound.
  Strict workflow: [42504110208](https://github.com/penghongzhong/HBL/actions/runs/42504110208).
- `ActualHartreeMatchedSpectralRegularizedQuadratic.lean` converts the
  actual matched profile's **weighted** bound to a genuinely zero-left-jet
  correction with quadratic spectral defect; this step **alone** does not
  produce the weighted bound from a physical orbit.
  Strict workflow: [42504361153](https://github.com/penghongzhong/HBL/actions/runs/42504361153).
- `ActualHartreeMatchedOriginalSourceWeightedSpectral.lean` derives
  **rather than assumes** the weighted first Cramer-matched profile from the
  original inverse-square source and actual Fredholm left Cauchy jet, then
  passes it into the zero-left regularized spectral gain.
  Strict workflow: [42504578042](https://github.com/penghongzhong/HBL/actions/runs/42504578042).

**Pending is not Success.** If any of these new workflows fails, inspect
the decoded strict job logs and repair the actual Lean file before accepting
any statement. An earlier run, [42501019413](https://github.com/penghongzhong/HBL/actions/runs/42501019413),
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
    [?] Derive uniform moving-radius first-profile bounds for SAME orbit
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
