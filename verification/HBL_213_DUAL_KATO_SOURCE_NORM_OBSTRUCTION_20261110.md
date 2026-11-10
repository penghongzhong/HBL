# HBL §2.13: decisive Kato source-norm obstruction (10 November 2026)

**Acceptance remains 11/13.** This is a paper proof / falsification of an unjustified implication, **not** a new Hartree PDE solution, not a Lean theorem, and not an external axiom. It does not relax the original revised §2.13 or Type-II main theorem. Pinned strict Lean statuses in the existing ledger are unchanged.

## 1. The exact Hartree phase block

For the original inverse-square quartic nonlinearity
\[
\mathcal N(u)=\kappa_{\rm H}(|x|^{-2}*|u|^4)|u|^2u,
\quad W=(1+|x|^2)^{-1/2},
\quad-\Delta W=\mathcal N(W),
\]
elementary radial differentiation gives \(-\Delta W=3W^5\). Since \(W>0\),
\[
\kappa_{\rm H}(|x|^{-2}*W^4)=3W^2.
\]
Consequently the **actual imaginary/phase Hessian**, without any local-NLS substitution, is
\[
L_-=-\Delta-3W^4.
\]
The real block is still genuinely nonlocal,
\[
L_+=-\Delta-9W^4
      -4\kappa_{\rm H}W^3(|x|^{-2}*(W^3\,\cdot)).
\]
This identity is a direct consequence of the original stationary Hartree PDE and the explicit bubble normalization. It is not a newly accepted Lean theorem.

## 2. Rigorous counterexample to a tempting but false norm upgrade

Kim, *Smooth radial quantized Type II blow-up for the three-dimensional energy-critical nonlinear Schrödinger equation* (arXiv:2610.26127, 19 October 2026), Proposition 4.2(2), requires a **Morawetz-dual energy functional** bound
\[
 |(Hg,F(s))|\le \psi(s)\|g\|_{\rm Mor}
\]
and does not say that arbitrary shell-weighted spatial \(L^2\) bounds imply this estimate. In the actual HBL phase block, the implication fails even on a single fixed, smooth annulus.

Choose a nonzero real \(\chi\in C_c^\infty((1,2))\) and define
\[
 F_N(r)=\chi(r)\sin(Nr),\qquad g_N(r)=N^{-1}F_N(r),
 \qquad N\in\mathbb N.
\]
All radial weights on \(1<r<2\), including HBL's shell \(7/4\)-weight, are bounded above and below. Therefore
\[
 \sup_N\|F_N\|_{L^2_{7/4}(1,2)}<\infty.
\]
Kim's radial Morawetz norm, equivalent to
\[
 \|g\|_{\rm Mor}^2\asymp
 \int_0^\infty
 \left(\frac{|\partial_r(rg)|^2}{\langle r\rangle^2}
       +\frac{|rg|^2}{\langle r\rangle^4}\right)dr,
\]
satisfies \(\sup_N\|g_N\|_{\rm Mor}<\infty\).
On the other hand, integration by parts in the three-dimensional radial measure gives
\[
\begin{aligned}
 (L_-g_N,F_N)_{L^2(\mathbb R^3)}
 &=\frac{4\pi}{N}\int_1^2
    \left(|F_N'(r)|^2-3W(r)^4|F_N(r)|^2\right)r^2\,dr\\
 &=2\pi N\int_1^2r^2\chi(r)^2\,dr+o(N)\longrightarrow+\infty .
\end{aligned}
\]
The asymptotic follows by \(F_N'=N\chi\cos Nr+\chi'\sin Nr\) and the Riemann–Lebesgue lemma. Thus **no uniform bound** of the form
\[
 \sup_{\|g\|_{\rm Mor}\le1}|(Hg,F)|
 \le C\|F\|_{L^2_{7/4}(1,2)}
\]
can be inferred even for the genuine Hartree phase Hessian. This example refutes only the claimed *automatic* norm upgrade; it does not refute the possibility of an improved estimate for the specially structured physical Hartree residual after projection.

## 3. Correct interface and shortest PDE gate

The desired dual Kato endpoint estimate requires **both**:

(A) the projected adjoint homogeneous smoothing estimate for the **actual** coupled Hartree generator on its nonresonant subspace,
\[
 \|A\,U_{\rm H}(\cdot)^*P_{\rm nr}h\|_{L_s^2Y}
 \le C_{\rm K}\|h\|_{\mathcal E},
\]
including a Hartree-specific positive-energy limiting-absorption bound, elimination of nonzero embedded eigenvalues and correct zero-threshold projection;

(B) the full SAME-ORBIT moving four-region nonlinear PDE source, including both moving interfaces, physical selection derivatives and all nonlocal mixed interactions, in the matching **adjoint range**:
\[
 P_{\rm nr}F_{\rm full}(s)=A^*q(s),\qquad
 \|q(s)\|_Y\le C_Fs^{-15/8}.
\]
A sufficient alternative to a direct factorization is a verified source functional
\[
 |(H_{\rm H}g,F_{\rm full}(s))|
 \le C_Fs^{-15/8}\|g\|_{\rm Mor}
\]
in the *correct Hartree energy and projected spaces*, with compatibility with the adjoint smoothing duality. In radial variables, a concrete candidate structural producer is a divergence representation analogous to Kim's (4.26),
\[
 r H_{\rm H}P_{\rm nr}F_{\rm full}(s)
 =-\partial_r\!\left(\frac{q_1(s,r)}{\langle r\rangle}\right)
   +\frac{q_2(s,r)}{\langle r\rangle^2},\quad
 \|q_1(s)\|_{L^2(dr)}+\|q_2(s)\|_{L^2(dr)}
 \lesssim s^{-15/8}.
\]
This last display is a **new proof obligation**, not a verified source identity or a theorem claim.

If (A) and (B) hold with the correct dual pairing, Cauchy–Schwarz on the dualized Duhamel tail gives the **conditional** pointwise energy estimate
\[
 \|\epsilon(s)\|_{\mathcal E}
 \le C_{\rm K}\biggl(\int_s^\infty\|q(\sigma)\|_Y^2d\sigma\biggr)^{1/2}
 \le\frac{2C_{\rm K}C_F}{\sqrt{11}}s^{-11/8}
 =O(s^{-1/4}s^{-9/8}).
\]
Important: Kim's **inhomogeneous** estimate (4.10) by itself is an \(L_t^2\mathrm{Mor}_x\) estimate, **not** an \(L_t^\infty\dot H_x^1\) estimate. The displayed endpoint requires the separate *homogeneous adjoint smoothing + source factorization* duality. It also requires stability under the truly moving Hartree coefficients and threshold-Lipschitz dependence before the finite-profile/PDE orbit is constructed.

The existing shell \(s^{-15/8}\) bound is a conditional static shell result, and it is currently in the wrong spatial source norm for (B). A successful scalar \(L^2_s\) power computation (CI 42776359428) does not bridge this gap. The original Hartree phase zero mode \(W\), scaling mode \(\Lambda W\), nonlocal real Hessian, and unstable modes must be treated correctly, not hidden in a free propagator assumption.

## 4. Exact Hartree phase/real Morawetz-dual source criterion (paper calculation; NOT a new Lean acceptance)

The preceding counterexample identifies a **missing derivative**, not just an
unspecified functional space. One can state an entirely explicit sufficient
spatial source condition using **both actual Hartree Hessian blocks**, without
replacing the nonlocal real block by NLS.

Write \(\mathcal I f=\kappa_{\rm H}(|x|^{-2}*f)\),
\(\langle r\rangle=(1+r^2)^{1/2}\),
\(v(r)=r g(r)\), and let \(F,g\) be real smooth compactly
supported radial test functions. The correct operators are
\[
 L_-g=-\Delta g-3W^4g,\qquad
 L_+g=-\Delta g-9W^4g-4W^3\mathcal I(W^3g).
\]
Radial integration by parts and symmetry of the **actual Riesz convolution**
give the following exact equalities:
\[
 \frac{\langle L_-g,F\rangle_{\mathbb R^3}}{4\pi}
 =\int_0^\infty\!
 \left[v'(r)\,rF'(r)
 -v(r)\bigl(F'(r)+3rW(r)^4F(r)\bigr)\right]dr,
\]
\[
 \frac{\langle L_+g,F\rangle_{\mathbb R^3}}{4\pi}
 =\int_0^\infty\!
 \left[v'(r)\,rF'(r)
 -v(r)\left(F'(r)+9rW(r)^4F(r)
 +4rW(r)^3\mathcal I(W^3F)(r)\right)\right]dr.
\]
Here \(r^2 g'=r v'-v\), and the symmetry step is
\(\langle W^3\mathcal I(W^3g),F\rangle
=\langle g,W^3\mathcal I(W^3F)\rangle\).
Define the explicitly weighted test norm
\[
 \|g\|_{{\rm Mor},0}^2
 =\int_0^\infty\!
 \left(\frac{|v'|^2}{\langle r\rangle^2}
 +\frac{|v|^2}{\langle r\rangle^4}\right)dr
\]
and the **sufficient**, not necessarily sharp, physical source norms
\[
 \begin{aligned}
 \mathcal D_-(F)
 &=\|\langle r\rangle\,rF'\|_{L^2(dr)}
   +\|\langle r\rangle^2(F'+3rW^4F)\|_{L^2(dr)},\\
 \mathcal D_+(F)
 &=\|\langle r\rangle\,rF'\|_{L^2(dr)}
   +\|\langle r\rangle^2
       (F'+9rW^4F+4rW^3\mathcal I(W^3F))\|_{L^2(dr)}.
 \end{aligned}
\]
Cauchy--Schwarz now proves, **with no hidden source-norm hypothesis**,
\[
 |\langle L_-g,F\rangle_{\mathbb R^3}|
 \le4\pi\|g\|_{{\rm Mor},0}\mathcal D_-(F),\qquad
 |\langle L_+g,F\rangle_{\mathbb R^3}|
 \le4\pi\|g\|_{{\rm Mor},0}\mathcal D_+(F).
\]
The Hamiltonian matrix bound follows by applying these to its two
components. The real-channel formula retains the full nonlocal integral.

**Precise, still OPEN physical producer:** for the actual, selected,
projected, moving four-region Hartree residual
\(F_{\rm full}=(F_1,F_2)\), prove a correctly projected and
moving-stable counterpart of
\[
 \mathcal D_-(F_1(s))+\mathcal D_+(F_2(s))
 \lesssim s^{-15/8}
\]
or a *weaker equivalent* bound in the dual space of the eventual
Hartree homogeneous smoothing theorem. The strong sufficient norm
above **cannot** be inferred from existing shell \(L^2_{7/4}\):
moving-cutoff radial derivatives, nonlocal cross-density and the
projection can lose powers. Nor does it establish the coupled
Hamiltonian adjoint Kato estimate, embedded-spectrum exclusion,
parameter Lipschitz, any new \(s^{-9/4}\) residual gain, an orbit,
or the Type-II rate. The identities in this section are human
paper algebra, not a compiled Lean theorem. Revised original
13-environment acceptance remains **11/13 (84.62%)**.

**Next direct producer:** prove the true four-piece moving source functional bound in (B), or produce the real four-piece linearized PDE inverse with source norm strictly better than the absolute-integration threshold; do not spend another run proving shell-power identities or abstract packet termination.

**Public evidence retained:** finite spectral four-piece PDE telescope CI 42536552509 is strict Success, but is an exact identity only. Original revised acceptance remains **11/13**. The final Type-II strong orbit and its dynamically selected rate remain unproved.
