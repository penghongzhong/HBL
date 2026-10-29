# HBL revised minimal main theorem — radial finite-time type II blowup

Date: 2026-10-29. This is a proposed, **NOT YET PROVED**, **NOT YET LEAN-ACCEPTED** replacement of the October 27 wide-range dynamical-rate main theorem. Do not overwrite the old source. Every new claim must eventually match a real Hartree PDE solution, not an abstract formal flow.

## Actual equation and criticality

\[
i\partial_tu+\Delta u+\kappa_{\rm H}\bigl(|x|^{-2}*|u|^4\bigr)|u|^2u=0
\quad\text{on }\mathbb R^3.
\]

Normalize \(\kappa_{\rm H}\) so \(W(x)=(1+|x|^2)^{-1/2}\) solves the elliptic ground-state equation. Write \(W_\lambda(x)=\lambda^{1/2}W(\lambda x)\); the critical norm \(\|\nabla W_\lambda\|_2=\|\nabla W\|_2>0\) is scale-independent.

## Proposed reduced unconditional main target

**Theorem (single radial type II blowup at one fixed nonresonant rate; OPEN).**

There exist \(0<t_0<T<\infty\), a radial strong solution
\[
u\in C([t_0,T);\dot H^1_{\rm rad}(\mathbb R^3))
\]
of the *actual* equation, a scale \(\lambda(t)>0\), phase \(\gamma(t)\), a terminal remainder \(\eta_T\in\dot H^1_{\rm rad}\), and
\(\eta\in C([t_0,T);\dot H^1_{\rm rad})\) such that

\[
u(t,x)=e^{i\gamma(t)}W_{\lambda(t)}(x)+\eta(t,x),\qquad
\eta(t)\to\eta_T\quad\text{in }\dot H^1
\]
as \(t\uparrow T\), with

\[
\lambda(t)^{-1}=C_\lambda(T-t)^{\frac12+\sqrt2}(1+o(1)),
\qquad C_\lambda>0,
\quad \gamma(t)=\gamma_T+o(1)
\]

and

\[
\sup_{t_0\le t<T}\|u(t)\|_{\dot H^1}<\infty,\qquad
\text{the maximal forward time interval ends at }T,\qquad
u(t)\text{ has no strong }\dot H^1\text{ limit at }T.
\]

This is **genuine energy-critical type II blowup**: finite time, finite critical norm, and noncompact concentration. The scale is faster than self-similar since \(1/2+\sqrt2>1/2\). In the original dynamical coordinates it corresponds to the one fixed parameter
\(\mu_\infty=\sqrt2/2>9/16\), \(\vartheta_\infty=0\), with terminal prescribed radiation \(g=0\), and a selected rather than arbitrary unstable coordinate. No \(C^1\) initial-data graph or universal parameter family is claimed.

The bubble energy density concentrates at the origin; **the exact measure limit** may be retained only after verifying bubble-radiation cross-term decoupling, not inferred from merely writing a decomposition.

For publication the eventual theorem must NOT list as hypotheses the existence of the exact orbit, its Type II behavior, or its final decomposition. Those are conclusions.

## Scope reduction from original target

- Fix just one irrational nonresonant speed, not every parameter in a compact set; phase target \(\vartheta_\infty=0\).
- Take terminal radiation \(g=0\) and one selected stable parameter (e.g. \(\alpha_-=0\)), rather than a ball of radiation and a complete \(C^1\) center-stable initial-data graph.
- Require energy-strong convergence of the remainder in \(\dot H^1\), not the previous extra \(\dot H^{1+9/16}\) limiting regularity for a whole family.
- Do not assert arbitrary energy proximity to \(E(W)\), exact measure decomposition, uniqueness of all shooting parameters, or full-rate-map regularity in the first main theorem.
- Retain the real physical PDE, \(T_+=T<\infty\), bounded \(\dot H^1\), a nontrivial concentrating \(W_\lambda\), and failure of strong continuation.

If one fixed irrational speed still proves overly costly, the next intellectually meaningful fallback is an existence theorem for **some** rate \(a>1/2\), without prescribing \(a\); however the actual radial Hartree solution must still be constructed.

## Analytic proof chain: every unverified premise is a TASK, not a new axiom

1. Fix the parameter in the already validated Kummer/Green regime. Use the strict 33-theorem origin Green/Frobenius block: Actions 40857582165.
2. Construct a finite three-region approximate profile \(V_N\) for the actual \(\mathcal N\) and its explicit residual in a physical source norm. Prove smallness, the weighted overlaps, and both threshold charges. No claim based on generic \`LayerPacket\` data.
3. Build the actual constrained Hartree evolution with the retained upper-triangular threshold coupling. **Do not** assume exact zero-centre block diagonalization or infer a Sylvester inverse merely from static coercivity.
4. Prove a genuine physical backward solver \(G\) and weighted source bounds (including parameter feedback), then the full nonlinear map is a contraction on a closed ball. Reuse existing abstract Banach fixed point sources only after the actual operator/source has been instantiated.
5. Reconstruct an exact strong radial PDE orbit (not just a function satisfying a formal integral identity) and select its unstable initial coordinate.
6. Prove scale asymptotics by the existing physical-clock Lean chain, bubble critical-energy invariance, energy-bound of the remainder and scale separation. The verified generic lemma \`HBL.MainBackward.no_strong_limit_of_separated_profile\` is useful, but actual \(W_\lambda\) separation still needs a proof.

## Audit policy

The new main conclusion is unconditional and remains **OPEN**. If an intermediate theorem states a conditional result from a parametrix/resolvent certificate, it must be labelled *conditional* and NOT counted as the original or revised main theorem. A proof of bounded energy plus an abstract nonextension criterion does not establish existence of the physical solution.

Historical original-manuscript acceptance: **9/21**. This is a changed theorem target, not a dishonest attempt to restore the historical 20/21 count by reducing denominators.

Lean pin: 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5. New theorem source must be strict \`--trust=0 -DwarningAsError=true\`, and transitive axioms restricted to \`propext\`, \`Classical.choice\`, \`Quot.sound\`.
