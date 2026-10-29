# HBL dynamical-rate selection — immediate true-PDE proof obligation

Date: 2026-10-29. Main theorem status: OPEN; historical original strict acceptance: 9/21.

## Exact kinematic requirements

For an actual strong radial solution, after deriving the rescaled Hartree PDE and identifying the scale/phase by the **actual two normalized test conditions**,

\[
  q=(T-t)\lambda^2,\quad b=\lambda_s/\lambda,\quad
  \mu=(2bq-1)/4,\quad q_s=4\mu
\]
and
\[
 \boxed{2\mu_s=q b_s+4b\mu.}
\]

The drift formula is pure calculus. It says that the **complete projected PDE forcing**, including threshold and radiation feedback, must control the combination \(q b_s+4b\mu\). The individual terms are not presumed integrable.

The proof must construct an actual forcing \(\mathfrak F_{\rm Hartree}[u]\) from the physical nonlocal operator and constraint equations, with an equality

\[
  q(s)b_s(s)+4 b(s)\mu(s)
     =2\mathfrak F_{\rm Hartree}[u](s)
\]

and an estimate

\[
 |\mathfrak F_{\rm Hartree}[u](s)|
   \le C s^{-1-\delta}
\]

from **actual physical residual, weighted overlap and feedback** estimates, not from a hypothesis with the desired decay built in. This gives the emergent limit

\[
 \mu_\infty
  =\mu(s_0)+\int_{s_0}^\infty\mathfrak F_{\rm Hartree}[u](s)\,ds.
\]

Choose an admissible **initial modulation window** with a margin above \(9/16\), then prove the total drift is smaller than that margin. The terminal value \(\mu_\infty\) is an output of dynamics, never a prescribed exponent.

For \(\mu_\infty>9/16\), the already verified clock/rate reconstruction yields
\[
  \lambda(t)^{-1}\sim C(u_0)(T-t)^{1/2+2\mu_\infty}.
\]
The original dynamical-rate research question is unchanged.

## Currently available actual-source evidence

The original accepted manuscript environment 2.6 contains
HBL.Modulation.Monopole.monopoleThresholdCoordinates_integrable.
It proves that both **actual normalized projections of the finite-cutoff
monopole *effective increment*** are time-integrable under stated
primitive-path decay assumptions on \(c,b,\omega\).
This effective increment has a displayed local cubic bookkeeping term
and **is not identical to the full physical Hartree residual of an exact orbit**.

The source terminal construction in
HBL/TypeIIDynamicSelection/MonopoleSourceTerminal.lean integrates those
particular projections, so its two terminal parameters exist as definite
source integrals, with no terminal limit in the hypotheses.
HBL/TypeIIDynamicSelection/MonopoleSelectedRate.lean maps that emergent
**monopole approximate-subsystem** limit to an instantaneous rate.
The exact formula for the actual physical modulation derivative is in
HBL/TypeIIDynamicSelection/ClockDrift.lean.

These new sources are pending strict Lean audit at the time of writing,
and **none** closes the physical feedback, PDE orbit existence or original
manuscript 2.12 / main target. In particular, proving a terminal limit
for the effective monopole subsystem is not an existence theorem for
a Hartree blowup orbit.

## Shortest actual load-bearing route

1. Compare the monopole effective increment to the **full** renormalized Hartree residual, including the moving Kummer/remote profiles and radiation: produce a precise signed identity for the remainder, with the actual physical nonlocal convolution and no substituted local cubic term.
2. Differentiate the two **physical** orthogonality constraints on the actual common domain, derive the \(2\times2\) coefficient system and prove its uniform invertibility for one admissible initial window.
3. Derive the forcing identity for \(q b_s+4b\mu\), and estimate the complete right-hand side using the matched profile, retained coupling and weighted backward solver.
4. Construct the true nonlinear fixed-point orbit. Control the actual source on that orbit, proving \(s^{-1-\delta}\) drift and \(\mu_\infty>9/16\).
5. Apply clock identities and actual energy-critical bubble separation to obtain finite-time type II blowup and a dynamically selected rate.

Until the full actual PDE forcing has been identified and estimated, do not claim any original-environment numerator improvement (9/21), an unconditional rate theorem, or a fixed asymptotic exponent.
