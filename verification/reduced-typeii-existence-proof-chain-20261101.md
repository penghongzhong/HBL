# HBL revised existence-only proof dependency ledger (2026-11-01)

## Exact scope — no disguised fixed blowup rate

Target: existence of **at least one genuine radial strong Hartree Type II
blowup orbit** whose rate exponent is an **output of the actual Hartree
modulation ODE**, not a prescribed terminal parameter.

Source target: \`verification/typeii-minimal-main-replacement.tex\`;
current historical strict environment audit:
\`verification/original-environment-audit-20261028.json\`.

## Safe deletion from the *revised* numbered chain

The old \`prop:center-stable-C1-v52\` (5.3) concerns a codimension-one
local C1 **family**, C1 shooting graph, initial-data chart and differentiable
rate map. None of those is an assumption or conclusion of the corrected
**single-orbit existence** target. Consequently 5.3 can be moved into an
optional *future strengthening* and excluded from the revised main theorem's
mandatory numbered proof chain.

Do **not** silently remove any of the still-needed physical PDE ingredients
(three-region actual profile, spectral Hamilton/zero-centre dynamics,
constrained Green evolution, nonlinear fixed point, scale noncompactness).
In particular the open old 2.12, 2.13, 2.14, 3.1, 3.2, 3.3, 3.4,
4.1, 4.2 and 5.2 cannot be declared proved by this pruning.

## Separate counting conventions

- **Historical original manuscript ledger:** 9/21, unchanged (42.86%).
  Eight previously withdrawn environments are NOT verified.
- **Proposed reduced existence-only numbered scope:** 20 retained
  environments after excluding only old 5.3. Of those, the *same* nine
  have historical strict acceptance, hence 9/20 = 45% **scope-adjusted**.
  The increase is ONLY denominator reduction, not a newly proved theorem.
- The proposed reduced count becomes an actual revised-manuscript count
  only after removing the old 5.3 numbered statement and all dependencies
  on it from the private TeX manuscript. This public Lean repository does
  not contain or publish the private paper TeX/PDF.
- **Newly closed historical original environments in this audit: zero.**

## High-value next candidate: old 5.2

\`HBL/WeightedJointBackward.lean\` already proves the genuine HBL
centre/threshold weighted fixed point for a standard constrained centre
propagator and source families \`E,G\` satisfying explicit decay and
Lipschitz hypotheses. The supplemental candidate
\`HBL/TypeIIDynamicSelection/ActualJointContraction.lean\` additionally
derives closed-ball invariance from the source-at-zero bound and the
proved contraction constant; no self-map assumption is inserted.

This candidate may serve as the **conditional nonlinear Banach step** of
a revised 5.2 theorem. It is NOT a fully accepted old 5.2 unless one
identifies its \`E,G,CE\` with the exact common-domain physical
Hartree covariant Green and total geometric/nonlinear source and
independently proves the required bounds from earlier main-chain
analytical estimates. It must NOT increase the 9/21 historical count
solely because a conditional weighted fixed point compiles.

## Short dependency spine

1. Real Hartree minimum-weight PDE source with one set of actual matched
   inner ± / Kummer / remote charges and positive new-term gains (old 2.12).
2. Physical finite profile, weighted source norm, Hessian and modulation
   Jacobian (old 2.13); global H1 algebraic branch extraction (old 2.14).
3. Actual retained zero-centre Hamilton generator and true slow perturbation
   estimates (old 3.x, avoiding invalid exact zero-centre splitting).
4. Source-aligned physical constrained Green propagator / geometric estimates
   (old 4.1 and necessary two-path control or a proved replacement).
5. Source-faithful weighted joint backward fixed point and shooting
   (old 5.2 and already accepted 5.1).
6. Exact PDE reconstruction, emergent positive terminal rate, finite
   time H1 boundedness and failure of strong continuation (revised main).

No new axiom, placeholder, or claimed main PDE existence is created
by this dependency audit.


## 2026-11-01 — Physical radiation moment versus moving-cutoff drift (new candidate)

Source: \`HBL/TypeIIDynamicSelection/ActualMomentCutoffTransport.lean\`.
**Verification status at writing: submitted for strict compilation, not yet counted.**

The previously strictly certified whole-radiation mass law reads, for
\(\ell=\lambda^{-1}\), \(c_g=\kappa_H\ell\,m_0[z_g(t)]\),
\[
\ell_s=-b\ell,\quad t_s=\ell^2,\quad
(c_g)_s=-bc_g+\kappa_H\ell^3\,\partial_t m_0[z_g(t)].
\]
The coefficient \`actualPhysicalRadiationMonopole\` is a genuine 3D
inverse-square quartic Hartree moment (not a freely prescribed rate)
and is NONNEGATIVE by the previously verified
\`actualRadiationCenter_nonneg\`, including its zero set.

Therefore the **actual original** monopole cutoff
\[
\eta(s,r)=1-\chi(|c_g(s)|r/4)
\]
coincides pointwise with \(1-\chi(c_g(s)r/4)\), avoiding
division by \(c_g\) or differentiating \(|c_g|\) at zero.
Ordinary chain rule gives the *source-identified* exact material
derivative
\[
(\partial_s+br\partial_r)\eta
=-\frac{r}{4}\,\kappa_H\ell^3\,
  (\partial_t m_0[z_g(t)])\,\chi'(c_g r/4).
\]
Thus the bare \(bc_g\) drift cancels algebraically; only the true
physical radiation moment derivative survives. This is a load-bearing
Hartree source simplification for old 2.12, but **not** an asserted
spatial/source norm bound.

On the transition support \(\chi'(c_gr/4)\neq0\), the already proved
smooth cutoff is supported where \(1\le c_gr/4\le 2\).
If \(c_g=\kappa_H\ell m_0>0\) and \(\partial_t m_0\) exists, then
\[
|(\partial_s+br\partial_r)\eta|
\le 2\ell^2\frac{|\partial_t m_0|}{m_0}
\|\chi'\|_\infty.
\]
Hence a **derived** positive source gain follows once the actual
regular radiation flow is shown to have \(m_0\ge m_*>0\) and a bounded
time derivative on a terminal window. One must not merely assume
\(m_0\ge m_*>0\) for all data: choose a single nonzero terminal
radiation \(g\), prove \(m_0[g]>0\), and use continuity of the exact
Hartree local flow. Converting the resulting \(\ell^2\) gain to a
specific \(s^{-\rho}\) gain must use the **dynamically derived**
modulation/clock, not a prescribed asymptotic rate.

Still open: true HBL current-weight source projection and simultaneous
physical Hartree/Fredholm/Kummer/remote matching, plus all other
generated-source gains. Historical original count remains 9/21.


## 2026-11-01 — Strict validation of the existing weighted joint-ball fixed point

At source commit \`75bac3e9fe5f44e87c9b07f51e9636c4aec8e1b2\`,
Lean built the complete \`actual_weighted_joint_ball_contraction\`
declaration and printed its full type plus only
\`propext, Classical.choice, Quot.sound\`. A focused workflow's
Python verifier initially failed on a false-negative check requiring
\`@HBL.TypeIIDynamicSelection....\` while \`#check\` prints the same
full type without \`@\`.

The source was **not altered** to work around the audit. The script
was corrected in \`1b8c319dbca1e0daf527d762489eb32ea572a33b\`
to accept the genuine Lean output syntax, and **Actions
\`41250357826\` completed SUCCESS**, with
\`lake build\`, \`--trust=0 -DwarningAsError=true\`, full
type and transitive axiom check.

This verifies the original HBL **weighted Banach centre/threshold
contraction mechanism**, including source-at-zero closed-ball invariance
and uniqueness. It remains **conditional** on input
\`StandardConstrainedCenterPropagator\` and weighted physical-source
estimates for \`E,G\`; it does NOT establish the original manuscript
5.2 synchronized full \`(h,Q)\` physical Hartree map or the whole
Type II PDE construction. Historical original acceptance stays 9/21.
