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
**Verification update:** source commit `5d394864472790544c4bf1517b47dee916a87058`, GitHub Actions `41250746509` **completed/success**. Strict pinned Lean 4.35.0-rc3 / Mathlib a98628e16 build: **4161 tasks**; exported full theorem types and transitive axiom audit checked `actualMomentInnerCutoff_space_hasDerivAt`, `actualMomentInnerCutoff_time_hasDerivAt`, and `actualMomentInnerCutoff_material_derivative`. Their only transitive axioms are `propext`, `Classical.choice`, `Quot.sound`. No sorry, admit, or new axiom. These are 3 auxiliary original-chain proofs, NOT an accepted complete manuscript environment.

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


## 2026-11-01 — original monopole profile source actually uses 3D Hartree moment

Strict source commit \`75228ecfe6ed11311845883f44da581b4f8cbda4\`,
GitHub Actions [\`41251672249\`](https://github.com/penghongzhong/HBL/actions/runs/41251672249):
**completed/success**, 4163 Lake tasks, full exported type audit and
\`--trust=0 -DwarningAsError=true\` checks; only axioms
\`propext\`, \`Classical.choice\`, \`Quot.sound\`.

The four new strict terminal declarations are

- \`actualMomentInnerCutoff_eq_original_absolute\`;
- \`actualMomentInnerCutoff_original_monopole_profile\`;
- \`actual_moment_monopole_profile_threeD_hasDerivAt\`;
- \`actual_moment_monopole_core_threeD_hasDerivAt\`.

All use the **same** actually constructed original paper profile
\`monopolePerturbedRadialProfile\`. They prove its amplitude is the
physical nonnegative whole-radiation inverse-square **3D** Hartree moment,
the cutoff equals the original \`1-cutoff(|c|r/4)\` including at
\`c=0\`, and the exact time tangent
\[
\partial_sV_c=(-bc+\kappa_H\ell^3 m'_0)\Xi_{\rm mon}(r)
[1-\chi(cr/4)-(cr/4)\chi'(cr/4)].
\]
On the true spatial core \`c*r/4 < 1\`, the square-bracket term
equals one, with no zero-crossing exception. No prescribed \(\mu_\infty\).

The **next** strict source candidate is
\`HBL/TypeIIDynamicSelection/ActualMomentCoreResidual.lean\`,
which substitutes this physical amplitude in the previously certified
quadratic real monopole residual and true radiation self-Riesz potential
bound. Its strict CI verdict must be checked before counting it.

**Remaining HBL original-2.12 analytic load:** prove the actual
Hartree regular-radiation moment \`HasDerivAt\` and norm estimates from
the selected strong flow, then treat the physical *linear* mixed quartic
charge \`4 V^3 Re Z\` with the **same** inner plus/minus Fredholm,
origin Kummer and remote boundary matching, and derive each generated
source's positive time order. This work does not, by itself, close an
additional original manuscript environment. Historical 9/21 unchanged.


## 2026-11-01 — True 3D-moment Hartree monopole plus radiation self-Riesz source

**Strict source commit** \`524be4e66b5e63459d094f6909325feb92dd87c4\`;
GitHub Actions [\`41252171482\`](https://github.com/penghongzhong/HBL/actions/runs/41252171482):
**completed/success**. Complete 4165-job Lake build and strict
\`--trust=0 -DwarningAsError=true\` full declaration-type and
transitive axiom audits. Two new kernel-checked declarations:

- \`HBL.TypeIIDynamicSelection.actual_threeD_moment_monopole_core_effective_residual_quadratic\`;
- \`HBL.TypeIIDynamicSelection.actual_threeD_moment_monopole_self_Hartree_source_quadratic\`.

For the **same physical** \(c(s)=\kappa_H\ell(s)m_0[z_g(t(s))]\),
original \`monopolePerturbedRadialProfile\`, \(Z_s=\sqrt{\ell}z_g(t,\ell r)\),
and genuine complex Hartree renormalized residual, prove together:

1. The exact original radial Hartree core quartic Riesz row is integrable,
under the already displayed and physically meaningful smallness/core
conditions; no abstract PDE source is injected.
2. The genuine original monopole static/effective PDE source has
quadratic residual after subtracting the **true** physical time/scale/
phase first-order source, with the amplitude derivative derived from
the original *three-dimensional* Hartree radiation moment.
3. Replacing the effective scalar cubic with the **actual full-radiation
self-density Riesz potential** introduces only its rigorously derived
radial \(O(r^2)\) center error. In precise terms,
\[
\|\mathcal R_{\rm self}(V_c,Z)-\mathcal L_{\rm first}
       (c,-bc+\kappa_H\ell^3m'_0,b,\omega)\|
\le C_{\rm mon}c(s)^2+
 \left(C_{\rm rad}(Z_s,M,D)r^2\right)
 (1+C_{\rm mon,profile})^3.
\]

Here \(\mathcal R_{\rm self}\) means the original core residual
plus **the pure radiation self-Riesz potential times \(V_c^3\)**.
It does NOT represent the full \(\mathcal R(V_c+Z)\): the actual
mixed quartic potential, the changed local cubic at \(V_c+Z\),
and the radiation's own time/spatial derivatives remain separate.
No false claim of full nonlinear cancellation is made.

Both theorem statements use only \`propext\`, \`Classical.choice\`,
\`Quot.sound\`; no sorry/admit/new axioms. The local radiation source
bounds remain conditional on the genuine measurable/weighted L2 and
origin-flatness hypotheses for the physical rescaled radiation and
on differentiability of the genuine 3D moment; none prescribes
the blowup rate.

**HISTORICAL ORIGINAL NUMBERED ACCEPTANCE: 9/21 — UNCHANGED.**
The revised existence-only candidate 9/20 results solely from
legitimately removing the unneeded old C1 centre-stable graph theorem,
not a new proof acceptance.

**Next shortest original-2.12 path:** Derive
\(m'_0=4\operatorname{Re}\int |z|^2\overline z\,z_t/|x|^2\,dx\)
from the actual Hartree high-regularity local flow. The cubic Hartree
nonlinearity is real-potential times \(z\), so its contribution to
the real derivative vanishes. By Hardy's inequality:
\[
|m'_0(t)|\le16\|z(t)\|_\infty^2\|\nabla z(t)\|_2
                      \|\nabla z_t(t)\|_2.
\]
Then connect the actual linear mixed density
\(4V_c^3\operatorname{Re}Z\) with the verified normalized inner
plus/minus Fredholm charges, origin Kummer and remote matching,
and prove actual positive time-weight gain for all regenerated terms.
The full PDE blowup orbit and dynamically selected limiting rate
remain open.
