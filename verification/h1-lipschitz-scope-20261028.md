# Physical H1 remainder and manuscript scope — 2026-10-28

## What the new terminal proves

`HBL.RegularRadiation.RemainderH1.physical_remainder_h1_lipschitz`
uses the actual inverse-square kernel, the complete seventh-degree Hartree
source and its exact Taylor remainder about a real background. Its target is
the classical Cartesian H1 norm, with the value and all three weak partial
derivatives in L2 and the integration-by-parts identity stated explicitly.

The input is the mixed first-order ball on C1 representatives:

\[
\|f\|_{X_{\rm mix}}
=\max\{\|f\|_2,\|Df\|_{L^2(\mathrm{op})},
         \|f\|_\infty,\|Df\|_{L^\infty(\mathrm{op})}\}.
\]

For `0 < r ≤ 1`, both perturbations in this ball satisfy

\[
\|\mathcal R_w(h)-\mathcal R_w(k)\|_{H^1}
\le\sqrt{3C_0}\,r\,\|h-k\|_{X_{\rm mix}}.
\]

The constant is explicit and depends only on kappa and the four background
bounds. The background is real C1, L4 and bounded, with bounded/L2 real
differential; background L2 is not required. Zero increments are included.
No nonlinear sample bound, approximation sequence or existence of a flow is
assumed. Eight-point exact interpolation preserves the quadratic factor;
the pre-existing full first-order source difference controls each sample.

`FirstOrderBall` includes the actual L2 membership fields. The Linfty
membership used in the real-valued `lpNorm` is proved from measurable bounded
fields. Thus neither the total definition of Bochner integrals nor the
real-valued norm at infinity substitutes for a finiteness proof.

## The manuscript graph space is different

The inspected manuscript fixes

\[
X_{\rm f}^{\rm sc}=\dot H^1_{\rm rad}\cap\dot H^{25/16}_{\rm rad}.
\]

It does not embed continuously into the mixed space above. For a nonzero
smooth compactly supported radial phi, the elementary scaling families

\[
f_\lambda(x)=\lambda^{-1/16}\phi(\lambda x),\qquad
g_R(x)=R^{-1/2}\phi(x/R)
\]

have bounded graph norms as their parameters tend to infinity, while
`‖D f_lambda‖_infty` grows like `lambda^(15/16)` and `‖g_R‖_2` grows like `R`.
These scaling observations are mathematical scope checks, not newly
registered Lean declarations or manuscript environments.

Consequently the mixed theorem cannot be installed directly as
`LocalizedCenterNonlinearMap.LocalCenterLipschitz`. The current
`ConstrainedCenterSpace` carries only the weaker homogeneous energy norm.
One must also construct the actual radial realization and projection,
identify the physical source, and prove uniform bounds and time continuity.

## Short next analytic route

For `K(x)=|x|^(-2)`, split at radius one. The useful source spaces are

\[
K_{\rm near}\in L^1\cap L^{25/17},\qquad
K_{\rm far}\in L^3\cap L^\infty.
\]

Hölder then controls the potential from `rho ∈ Linfty ∩ L^(3/2)`,
and its derivative potential from `D rho ∈ L1 ∩ L^(25/8)`. This avoids
requiring either the field's L2 norm or its derivative's Linfty norm.
For quartic densities, use `f ∈ L6 ∩ Linfty` and
`Df ∈ L2 ∩ L^(25/8)`. Complete source differences and the non-L1 density
derivative realization must still be proved before the existing polynomial
interpolation can be instantiated under these weaker assumptions.

The choice `25/8 > 3` is strictly below the fractional Sobolev endpoint
`16/5`. A possible short embedding proof is a real Fourier dyadic
construction with L2/Linfty interpolation on each block. The low- and
high-frequency geometric factors are respectively `2^(27j/50)` and
`2^(-9j/400)`. This is an analytic route to be formalized, not an already
proved graph-space embedding.

At the pinned Mathlib revision, `SobolevInequality.lean` supplies integer
compact-core GNS, and the repository already supplies a physical L6
realization of the radial homogeneous energy completion. The existing
`MemSobolev` and `BesselPotentialSpace` interfaces are inhomogeneous.
No homogeneous graph-space realization is supplied by the new theorem.

Care is required with the general distribution Fourier-multiplier API:
`SchwartzMap.smulLeftCLM` is defined as zero when its multiplier does not
have temperate growth; that property includes smoothness at the origin.
The nonsmooth homogeneous symbol `|xi|^(25/16)` must therefore not be
inserted into this API and treated as the actual fractional derivative.
Use a justified weighted Fourier L2 realization or an appropriate domain.

## Environment accounting

`HBL.Kinematic.kinematicRecovery_originalEnvironment_closed` contains the
entire original `prop:kinematic-recovery-v2`: every permitted shift and
later time, clock bounds, absolute tail convergence, a concrete unique
physical synchronized root, and both quantitative estimates.
It revalidates one historical environment and does not add a new one.

`original-environment-audit-20261028.json` preserves all 21 original labels.
The remaining historical statements have not all been independently
reaudited, and eight old statements were withdrawn rather than proved.
No current whole-paper fraction or main-theorem completion is certified.
The exact compiler, source hashes, full elaborated types and transitive
axioms are recorded separately by `remainder_h1_lipschitz_validation.py`.
