# HBL 2.13: fixed-domain source stability, exact acceptance and scope

Date: 2026-11-11. Branch: `hbl-213-spectral-c1-trace-20261109`.

## Original environment boundary

**11/13 remains unchanged.** Neither this operator bridge nor the exact nonlinear telescope proves the full four-region weighted positive-time residual, its actual two-parameter Lipschitz estimate, the finite nonlinear profile recursion, or the dynamically derived Type-II rate. Environment 2.13 and the original final theorem are not accepted by this record.

## Actual strict acceptance: source-derived pointwise parameter stability

- Source commit: `de4223e7f35fd5eb3d40f0d0feb75acfc8303818`.
- Source: `HBL/TypeIIDynamicSelection/ActualHartreeKummerFixedDomainParameterStability.lean`.
- Source Git blob: `47634106482e3d8cb23dc75d94410f001995d2e6`.
- Workflow: `.github/workflows/hbl-213-fixed-domain-kummer-stability.yml`.
- Run: [42959428731](https://github.com/penghongzhong/HBL/actions/runs/42959428731), **Success**.
- Original job: `130322170093`; the complete original job log has been read, not merely the run badge.
- Evidence artifact: `13828428094`, `hbl-fixed-domain-kummer-parameter-strict-evidence`.
- Artifact ZIP SHA256: `3d3c43959c90b32bf580ba3774a33febc67b40323509bafa7cdd4ffa42fad2b3`.
- Compiler: Lean `4.35.0-rc3`, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib: `a98628e16c11f5167f16124105ddce53efa9bfe5`, explicitly checked against the actual dependency HEAD.
- Actual strict commands: `lake env lean --trust=0 -DwarningAsError=true` on the source and the separate audit. The source strict log is empty.
- Untruncated `#check` used `pp.all true` and `pp.maxSteps 10000000`.
- Each named `#print axioms` contains exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, `Lean.ofReduceBool`, admit or extra axiom.

The exact declarations audited individually are:

```text
HBL.TypeIIDynamicSelection.actual_Kummer_parameter_difference_exact
HBL.TypeIIDynamicSelection.actual_Kummer_fixed_domain_source_parameter_stability
```

The failed first run `42958970486`, original job `130320700981`, was inspected. Its genuine error at line 95 was an additive-monotonicity proof orientation. The repair replaces `apply add_le_add_right` by `refine add_le_add ?_ (le_refl _)`. No theorem hypothesis was weakened, and no axiom or placeholder was added. The repaired source was actually recompiled by the successful run above.

### Statement-level interpretation

Write

\[
K_jd=\Delta_rd+a_j^{-2}(ir d'/2+c_jd),\qquad
\lambda_j=a_j^{-2},\qquad c_j=\mathrm{frozenZeroCoeff}(\mu_j,\theta_j).
\]

On the common annulus \([R,2R]\), both fields have zero value and first derivative at the **same** anchor \(r_0\in[R,2R]\). The explicit smallness is

\[
16R^2(1+|c_j|)/a_j^2\le1\quad(j=1,2).
\]

The only quantitative field inputs are the complete operator-source bounds

\[
|K_2v|\le A_2,\qquad |K_1u-K_2v|\le A_{12}.
\]

Set

\[
Q=|\lambda_1-\lambda_2|+|\lambda_1c_1-\lambda_2c_2|,
\quad A=A_{12}+8R^2A_2Q,
\quad d=u-v.
\]

The actual conclusion is

\[
|\Delta_rd|\le2A,\qquad |d|\le8R^2A,\qquad |d'|\le8RA,
\]

and, for the existing genuine smooth overlap cutoff,

\[
|\Delta_r(\chi_Rd)-\chi_R\Delta_rd|\le CA
\]

with a universal positive cutoff constant. The value and slope bounds of the comparison field are produced by the existing zero-jet source estimate; they are not separate hypotheses. Classical second derivatives are used, not third jets at the interface.

**Scope restriction:** these two source inequalities are still hypotheses of this operator theorem. Producing them, with the required time order, for the selected nonlinear Hartree trajectory is not accomplished by renaming them as actual sources. This theorem alone is not the original parameter-Lipschitz statement.

## Actual strict revalidation: same-anchor field, three C1 joins and telescope

- Source commit: `773a43295085c6c132a80daa88e2ddf6576a63d6`.
- Run: [42958494409](https://github.com/penghongzhong/HBL/actions/runs/42958494409), **Success**.
- Original job: `130319187052`; complete original log read.
- Artifact: `13828860296`, `hbl-spectral-four-piece-nonlinear-PDE-telescope-evidence`.
- Artifact ZIP SHA256: `6b0be3c7c1f66701da7559796ece4415b9e5eae55f2248afc072be2407e014e3`.
- The corrected dependency graph was rebuilt, followed by strict source checks for the pullback, four-piece three-C1 and finite PDE telescope modules.
- The same pinned compiler, exact Mathlib HEAD, trust level, warning-as-error, untruncated type and individual allowed-axiom checks passed.

The exact four declarations are:

```text
HBL.TypeIIDynamicSelection.actual_Hartree_matched_Kummer_pullback_classical
HBL.TypeIIDynamicSelection.actual_Hartree_moment_locked_pullback_actual_inner_jet
HBL.TypeIIDynamicSelection.actual_Hartree_spectral_inner_four_piece_three_C1_joins
HBL.TypeIIDynamicSelection.actual_Hartree_finite_spectral_Fredholm_four_piece_full_PDE_telescopes
```

The original run `42530158681`, job `128882355120`, failed in a then-unrepaired C1 dependency before reaching the telescope. Its raw errors concerned the `InWeightedL2` namespace and an actual `HasDerivAt` definitional-equality mismatch. Those current dependencies now compile. The telescope remains an exact identity, **not** a residual gain.

## Corrected shortest proof route

The classical matched Kummer field already solves its original equation at every positive radius below the basis radius, including points to the left of the original anchor. Therefore restriction to the backward overlap \([L/2,L]\) preserves the original anchor \(L\), genuine Fredholm jets and original compatibility selection. A new selection is **not** needed just to define this overlap. This supersedes the re-anchoring prerequisite in the earlier forward-overlap note.

Actual smoothing changes the physical profile and hence the nonlocal source. That feedback must still be propagated into the genuine compatibility equations; it is not removed by retaining the anchor.

The accompanying paper proof is

`verification/HBL_213_FIXED_DOMAIN_SOURCE_STABILITY_20261111.tex`.

It establishes a fixed-domain radial Volterra inverse on \([1/2,1]\), explicit source-to-field Hilbert-space parameter estimates, strong time differentiation when the actual source and coefficients are C1, and estimates of the true moving smoothing perturbation. It also derives the complete nonlocal Hartree feedback and its quadratic remainder in the dual-energy norm. These Hilbert-space/time/nonlocal arguments are **paper proofs, not Lean acceptance**. In particular the dual-energy topology does not replace the original weighted residual topology.

The remaining necessary production is the actual source

\[
f(s,x)=L(s)^2\bigl(\mathcal T-\mathcal O+a^{-2}\delta u_0\bigr)(s,L(s)x)
\]

and its time and parameter differences from the same physical Hartree trajectory and the same unique real two-channel speed. No independent bound on \(f_s\), no positive time order and no blowup rate may be assumed. The subsequent full four-region weighted gain, finite recursion and final dynamic rate are still unaccepted.


## 2026-11-11 applicability correction: real matched jets are not individually zero

A statement-level issue was detected during the actual-source audit. The accepted theorem `actual_Kummer_fixed_domain_source_parameter_stability` assumes `u r0=0, deriv u r0=0, v r0=0, deriv v r0=0`. However the original matched Fredholm/Kummer physical fields satisfy only `u(r0)=v(r0)=U` and `u'(r0)=v'(r0)=V`, usually **nonzero**; see exact strict producer `actual_Hartree_moment_locked_pullback_actual_inner_jet`. Its zero-jet *difference* cannot by itself discharge the four hypotheses of the parameter theorem.

The manuscript supplement `verification/HBL_213_FIXED_DOMAIN_SOURCE_STABILITY_20261111.tex` now derives a **paper-level** explicit harmonic Cauchy lift
[
H_{U,V}(r)=U+r_0V(1-r_0/r),\qquad H(r_0)=U,\quad H'(r_0)=V,\quad \Delta_rH=0.
]
On `[R,2R]` with `r0 in [R,2R]` its Kummer source is bounded by
[
|K_{a,c}H|\le a^{-2}(|c||U|+2R(1+|c|)|V|),
]
**without any inverse left-radius Laplacian loss**. Applying the previously accepted zero-jet source estimate to the two lifted differences yields explicit parameter comparison estimates involving the genuine jet differences `Delta U`, `Delta V` and the full actual operator source difference, rather than assuming each physical field has zero jet. It also includes the exact derivative of this lift when the physical anchor moves.

**Acceptance:** the harmonic-lift extension has not been Lean-compiled or individually audited; no new Lean theorem or original environment is counted. The already accepted theorem remains correct with its *actual stronger hypotheses*. For §2.13 the remaining proof obligation is to control the **real** Fredholm jets and their time/parameter differences, the shared quartic nonlocal Hartree source, and the nonzero-jet lift in the original strong residual topology, thereby establishing a positive time order. The original revised ledger remains **11/13**.
