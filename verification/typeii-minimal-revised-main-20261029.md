# HBL: revised main theorem with dynamically selected Type II blowup rate

**Correction dated 2026-10-29.** The prior fixed-speed proposal, which imposed ν=√2 and μ∞=√2/2, is **withdrawn as the main research target**. It improperly replaced selection by the Hartree dynamics with construction at a prescribed exponent. The new, unproved main target is saved in verification/typeii-minimal-main-replacement.tex.

## Actual Hartree equation

\[
 i\partial_tu+\Delta u+\kappa_{\rm H}(|x|^{-2}*|u|^4)|u|^2u=0,\quad
 W(x)=(1+|x|^2)^{-1/2}.
\]

The revised target still **concludes existence of a true strong radial Hartree solution** with a finite maximal time, one concentrating ground-state bubble, bounded critical homogeneous H1 norm, convergent homogeneous H1 radiation and no strong H1 extension. None of these may be made a hypothesis or a new axiom.

## Dynamical selection — not a prescribed terminal exponent

The modulation scale and phase must be canonically extracted from the actual solution using its two threshold orthogonality conditions. With

\[
 \frac{ds}{dt}=\lambda^2,\quad
 \tau=T-t,\quad
 b=\lambda_s/\lambda,\quad
 \omega=-\gamma_s,\quad
 q=\tau\lambda^2,\quad
 \mu=(2bq-1)/4,\quad
 \vartheta=q\omega,
\]

the chain rule yields exact kinematic identities

\[
 \tau_s=-\lambda^{-2},\quad
 q_s=-1+2bq=4\mu,\quad
 (\log\tau)_s=-q^{-1},\quad
 (\log\lambda)_s=b=\frac{1+4\mu}{2q},
\]

and hence

\[
 \boxed{\frac{d\log\lambda^{-1}}{d\log(T-t)}
       =bq=\frac12+2\mu(s).}
\]

**The essential nonlinear task** is to prove from the actual Hartree modulation equations that the selected solution has \(|\mu_s(s)|\le C s^{-1-\delta}\), an emergent limit \(\mu_\infty=\lim_{s\to\infty}\mu(s)>9/16\), and that its source conditions are genuinely satisfied. No value of \(\mu_\infty\), \(\nu\), or the limiting exponent is imposed at the beginning.

Given those true PDE conclusions (not merely assumed input), integration gives

\[
 q(s)=4\mu_\infty s+O(s^{1-\delta}),\quad
 \lambda(t)^{-1}
 =C_\lambda(u_0)(T-t)^{a_\infty(u_0)}(1+o(1)),\quad
 a_\infty(u_0)=\tfrac12+2\mu_\infty(u_0).
\]

Positivity of the output \(\mu_\infty\) can follow from a chosen **initial** modulation window above 9/16 together with a proved small total dynamical drift, never from prescribing the limit. For finite-order profile nonresonance, one may choose an initial-data interval disjoint from the finitely many resonances relevant to that order and prove the drift stays inside; alternatively include logarithmic resonant terms. This is an analytic obligation, not yet an accomplished result.

## Shortest useful proof dependency chain

1. Construct a finite physical Hartree three-region parametrix and prove its actual residual/threshold charges. Reuse the already audited origin-normalized Kummer/Green and Frobenius components.
2. Derive the **true** two-channel modulation ODE from the physical Hartree equation; prove the integrable bound on \(\mu_s\) and positivity of its emergent limit without prescribed asymptotic data.
3. Build the genuine common-domain constrained Hamiltonian evolution with retained triangular threshold coupling, not the withdrawn exact zero-centre splitting.
4. Construct and contract the actual weighted nonlinear backward map. Select the unstable mode by a physical shooting equation and reconstruct an exact radial Hartree solution.
5. Apply the proven kinematic relations and bubble scale noncompactness to conclude a dynamically selected power-law exponent, bounded critical norm and finite-time Type II blowup.

## Reduced scope that does NOT alter the research question

We may drop the earlier theorem's full compact range of arbitrarily specified terminal parameters, every small radiation datum, global uniqueness across all fibres, and the codimension-one C1 initial-data graph. The first theorem need only assert **existence of at least one dynamically selected Type II orbit**. A subsequent strengthening may prove two different initial data yield different output exponents or continuity of the rate map. Neither is required for the first milestone.

## Strict verification boundary

The previously successful six fixed-speed Lean terminal lemmas (Actions 40866180583) remain true auxiliary statements, but **do not establish dynamic selection**. Historical full original-environment acceptance stays **9/21**. The new PDE existence and emergent-\(\mu_\infty\) theorem is **OPEN**. The next Lean task is to certify the unprescribed clock identity, then connect its assumptions to actual physical Hartree modulation; a formal algebraic clock theorem does not by itself prove any nonlinear orbit exists.

Pinned compiler Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5; strict trust-zero, warning-as-error and complete transitive axiom audit. No sorry, admit or novel axiom.
