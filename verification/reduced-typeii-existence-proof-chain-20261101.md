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
