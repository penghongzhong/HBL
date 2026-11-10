# HBL §2.13 — finite four-region and finite-layer NONLOCAL Hartree mixed interactions without an independent envelope

**10 November 2026.** Original \(\mathcal N(V)=\mathcal I(|V|^4)|V|^2V\), \(\mathcal I f=(3/\pi^2)|x|^{-2}*f\). This is a paper-level corollary of the *proved-on-paper, published-\(A_2\)-input* original-nonlinearity Lipschitz inequality (N31) in \`HBL_213_FULL_NONLINEAR_HARTREE_A2_SOURCE_DIFFERENCE_20261110.md\`, not a newly audited Lean theorem and not a PDE orbit. **Strict original environment count remains 11/13.**

## 1. Actual source space and a single nonlinear increment estimate

On radial complex functions, set
\[
 \|u\|_X:=\|u\|_{L^2(dr)}
       +\|(1+r^2)u'\|_{L^2(dr)},\qquad
 \|F\|_Y:=\|F\|_{L^2(dr)}
       +\|(1+r^2)F'\|_{L^2(dr)}.
\]
Functions in \(X\) are taken locally absolutely continuous with their actual weak derivative and limit zero at infinity; the latter follows from \(\|u\|_2<\infty\) and the weighted derivative bound (N13).

For each \(R<\infty\), the true original three-dimensional quartic Riesz map satisfies
\[
 \boxed{\quad
  \|\mathcal N(W+u)-\mathcal N(W+v)\|_Y
  \le C_R\|u-v\|_X,\quad
  \|u\|_X+\|v\|_X\le R ,
 \quad}
 \tag{F1}
\]
with an explicit finite \(C_R\) obtainable from (N23)–(N31) and the **single published** weighted \(A_2\) Riesz constant. No \(\|\partial_r\mathcal I\rho\|\) is supplied as an extra assumption. This inequality retains the entire real nonlocal kernel and is *not* a local-NLS surrogate. The \(Y\)-derivative is the true distributional derivative of the full nonlinear source.

## 2. Finite telescoping estimates that retain *all* quartic cross-density terms

For any **actual physical** base field \(V_0\) and corrections \(p_1,\ldots,p_n\) from the *same* PDE, define
\[
 V_j=V_0+\sum_{k=1}^jp_k,\qquad
 u_j=V_j-W,\qquad u_0=V_0-W .
\]
Assume only the explicitly checkable **profile** budget
\[
 \max_{0\le j\le n}\|u_j\|_X\le R .
 \tag{F2}
\]
This is **not** an assumed source bound: it is a necessary, still-to-be-proved physical estimate for the selected Fredholm/Kummer/repaired fields. Equation (F1), applied to the true pair \(u_j,u_{j-1}\), gives
\[
 \boxed{\quad
 \|\mathcal N(V_j)-\mathcal N(V_{j-1})\|_Y
 \le C_{2R}\|p_j\|_X .
 \quad}
 \tag{F3}
\]
(The same constant \(C_{2R}\) is valid because
\(\|u_j\|_X+\|u_{j-1}\|_X\le2R\).)
The complete original **nonlinear** finite telescope,
\[
 \mathcal N(V_n)-\mathcal N(V_0)
 =\sum_{j=1}^n[\mathcal N(V_j)-\mathcal N(V_{j-1})],
 \tag{F4}
\]
therefore obeys
\[
 \boxed{\quad
 \|\mathcal N(V_n)-\mathcal N(V_0)\|_Y
 \le C_{2R}\sum_{j=1}^n\|p_j\|_X.
 \quad}
 \tag{F5}
\]
Every mixed nonlocal cross term
\(\mathcal I(|V_{j-1}+p_j|^4-|V_{j-1}|^4)\)
is **inside the left side** of (F3), not discarded or separately bounded by an unproved cross-interaction assumption. No claim of linear superposition is made; the identity (F4) is simply an exact telescoping difference of the **full** original nonlinear map.

This applies to the real four-region/source-selected packet implementation only **after** the true partial sums \(V_j\) have been shown to lie in \(W+X\). The current public Lean finite PDE telescope certifies its algebraic structure, but does **not** establish (F2), (F3), full Sobolev regularity, or temporal decay. C² matching of value/slope/curvature alone does not imply \(\|p_j\|_X\) is sufficiently small.

## 3. Parameter and temporal application — exact remaining domain of proof

For any same-orbit parameter-dependent profile \(V_\alpha\),
\[
 \boxed{\quad
 \|\mathcal N(V_\alpha)-\mathcal N(V_\beta)\|_Y
 \le C_{2R}\|V_\alpha-V_\beta\|_X,
 \quad
 \sup_\gamma\|V_\gamma-W\|_X\le R .
 \quad}
 \tag{F6}
\]
This is a genuine source-Lipschitz *implication*, not an assertion that the selected physical profile itself is Lipschitz. The moving-\(L\) source transport in (V26) of
\`HBL_213_BACKWARD_FLAT_OVERLAP_VOLterra_PDE_GRADIENT_20261110.md\`
still requires \(\partial_\alpha V\) and the true time/modulation derivatives.

If the PDE-derived field bounds in (F2) and the \(p_j\) source sizes have an actual positive time exponent, (F5) propagates that exponent through **all complete Hartree nonlinear cross interactions** with no extra positive-order assumption on the Riesz kernel. **At present these profile/time estimates have not been obtained.** Other parts of the full PDE residual — the radial Laplacian, all moving interfaces, the original spectral corrections, local time/parameter transport and the unstable/continuous projections — are still independent, load-bearing gates. Even with (F5), a valid physical energy inverse/adjoint Hartree smoothing, a true nonlinear orbit, and dynamically emerging Type-II rate remain essential.

**Proved here at paper level:** a concrete reduction of the finite nonlocal Hartree mixed-interaction source estimate to the *actual selected profile* \(X\)-budget, via the published weighted Riesz theorem; the whole quartic kernel is retained.

**NOT proved:** the physical \(X\)-budget, residual time positive gain, parameter transport, Hartree projected inverse, strong orbit or final theorem. No new Lean axiom, no original environment increment. **11/13 (84.62%).**


## 4. Exact time differentiation of the original nonlinear Riesz term under a moving bubble

The **same original** nonlinear quartic Hartree map has a
strict scale covariance, independent of any chosen Type-II rate:
\[
 V_\lambda(s,r)=\lambda(s)^{-1/2}V(s,r/\lambda(s)),
 \quad
 \mathcal N(V_\lambda)(s,r)
 =\lambda(s)^{-5/2}\mathcal N(V(s,\cdot))(r/\lambda(s)).
\tag{F7}
\]
For a correction \(u(s)\) define the genuine bubble-subtracted source
\(\mathscr R(u)=\mathcal N(W+u)-\mathcal N(W)\).
Under the same scale,
\(\mathscr R_\lambda(s,r)=\lambda^{-5/2}
\mathscr R(u(s))(r/\lambda)\).
Writing \(\rho=r/\lambda(s)\), the ordinary chain rule yields
the **exact material time derivative**
\[
 \boxed{\quad
 \partial_s\mathscr R_\lambda(s,r)
 =\lambda^{-5/2}\left[
 D\mathscr R(u)[\partial_s u](\rho)
 -\frac{\lambda_s}{\lambda}
   \left(\frac52\mathscr R(u)(\rho)
          +\rho\partial_\rho\mathscr R(u)(\rho)\right)
 \right].
 \quad}
 \tag{F8}
\]
Here the complex-real Fréchet derivative is *not* replaced
by a local-NLS expression. It is determined by
\[
 \begin{aligned}
 D\mathcal N(V)[h]
 &=\mathcal I\bigl(4|V|^2
       \operatorname{Re}(\overline Vh)\bigr)\,|V|^2V\\
 &\quad+\mathcal I(|V|^4)
     \bigl(|V|^2h+
          2\operatorname{Re}(\overline Vh)V\bigr),\\
 D\mathscr R(u)[h]&=D\mathcal N(W+u)[h].
 \end{aligned}
 \tag{F9}
\]
The derivative is real-Fréchet on complex radial
functions; the \(A_2\) estimates underlying (F1)
give \(\|D\mathscr R(u)[h]\|_Y\le C_R\|h\|_X\)
on bounded \(X\) balls by differentiation of the
explicit polynomial/Riesz expression (or by the
difference estimate and a justified smooth limit).

For every \(F\in Y\), the elementary scale-invariant
radial inequality
\[
 \|\,\rho F'(\rho)\,\|_{L^2(d\rho)}
 \le\tfrac12\|(1+\rho^2)F'(\rho)\|_2
 \quad\bigl(2\rho\le1+\rho^2\bigr)
\]
gives, with **no independent nonlocal source derivative**,
\[
 \boxed{\begin{aligned}
 \|\partial_s\mathscr R_\lambda(s)\|_{L^2(dr)}
 \le \lambda^{-2}\Big[
 &C_R\|\partial_su(s)\|_X\\
 &+\Big|\frac{\lambda_s}{\lambda}\Big|
  \bigl(\tfrac52\|\mathscr R(u(s))\|_2
       +\tfrac12\|(1+\rho^2)
             \partial_\rho\mathscr R(u(s))\|_2\bigr)
 \Big].
 \end{aligned}}\tag{F10}
\]
The \(\lambda^{-2}\) factor follows from
\(dr=\lambda\,d\rho\) and the original
\(\lambda^{-5/2}\) Hartree critical scaling.

**Load-bearing limitation:** (F8)–(F10) require
the *actual* normalized physical profile to possess
\(\partial_su\in X\) and its *PDE-selected* scale to
possess \(\lambda_s/\lambda\); the current source-selected
static Green/Cramer and \(C^2\) interface proofs do
**not** produce either quantitative bound. The moving
Kummer endpoints, selected two-channel speed and
full nonlinear evolution are embedded in
\(\partial_su\), and are not made small by this algebra.
This is a correctly normalized **paper-level
nonlocal source time-chain identity**, not a claimed
new positive time order or Lean CI. Original count
**11/13**.
