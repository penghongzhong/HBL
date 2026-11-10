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


## 5. Explicit radial Riesz Hilbert--Schmidt constant: the nonlocal term itself costs NO extra shell radius

The sufficient norms in §4 can be reduced further. With the physical
bubble normalization \(W=(1+r^2)^{-1/2}\), evaluation of its stationary
equation at the origin gives the **fixed** coupling
\[
 3=-\Delta W(0)=\mathcal I(W^4)(0)
 =4\pi\kappa_{\rm H}\int_0^\infty(1+s^2)^{-2}ds
 =\pi^2\kappa_{\rm H},
 \qquad \kappa_{\rm H}=\frac3{\pi^2}.
\]
For radial \(F\) and \(r,s>0\), exact angular integration yields
\[
 \mathcal I(W^3F)(r)
   =\int_0^\infty K(r,s)F(s)\,ds,\qquad
 K(r,s)=2\pi\kappa_{\rm H}W(s)^3
       \frac{s}{r}\log\frac{r+s}{|r-s|}.
\]
Set \(h(t)=t^{-1}\log\frac{1+t}{|1-t|}\).
The substitutions \(t=\tanh u\) on \((0,1)\) and
\(t=\coth u\) on \((1,\infty)\) give the exact integral
\[
 \int_0^\infty h(t)^2dt
 =4\int_0^\infty u^2
      \left(\frac1{\sinh^2u}+\frac1{\cosh^2u}\right)du
 =4\bigl(\zeta(2)+\eta(2)\bigr)=\pi^2,
\]
where \(\eta(2)=\sum_{n\ge1}(-1)^{n-1}/n^2=\pi^2/12\).
Since \(\int_0^\infty sW(s)^6ds=1/4\), Tonelli and \(r=st\)
prove the actual Hilbert--Schmidt identity
\[
 \begin{aligned}
 \int_0^\infty\!\int_0^\infty |K(r,s)|^2\,dr\,ds
 &=(2\pi\kappa_{\rm H})^2
    \left(\int_0^\infty sW(s)^6ds\right)
    \left(\int_0^\infty h(t)^2dt\right)\\
 &=\pi^4\kappa_{\rm H}^2=9.
 \end{aligned}
\]
Consequently, in the **one-dimensional radial measure \(dr\)**
(rather than the physical \(r^2dr\) measure),
\[
 \boxed{\ 
 \|\mathcal I(W^3F)\|_{L^2(dr)}
 \le 3\|F\|_{L^2(dr)}.
 \ }
\]
This coefficient is exact as a Hilbert--Schmidt **upper bound**, not
an assertion that the operator norm equals \(3\).

The pointwise weights satisfy
\[
 \langle r\rangle r\le\langle r\rangle^2,\qquad
 \langle r\rangle^2rW^4=\frac r{1+r^2}\le\frac12,\qquad
 \langle r\rangle^2rW^3=\frac r{\sqrt{1+r^2}}\le1.
\]
Substitution into §4 therefore yields the explicit two-channel bounds
\[
 \boxed{\begin{aligned}
 \mathcal D_-(F)&\le
       2\|\langle r\rangle^2F'\|_{L^2(dr)}
       +\frac32\|F\|_{L^2(dr)},\\
 \mathcal D_+(F)&\le
       2\|\langle r\rangle^2F'\|_{L^2(dr)}
       +\frac{33}{2}\|F\|_{L^2(dr)}.
 \end{aligned}}
\]
Thus the **nonlocal Hartree Hessian itself does not require a new
independent Riesz source envelope** for this sufficient dual estimate:
it is uniformly bounded by the *unweighted radial source \(L^2\)*.
The true remaining missing source producer is its
**weighted radial derivative**, at the actual moving physical scales
and after the genuine nonresonant projection, in addition to the
separate homogeneous adjoint Kato/spectral gate. This is a useful
analytic narrowing but **does not** prove that the actual residual
meets the required \(O(s^{-15/8})\) norm, construct a Hartree orbit,
or justify an increase from **11/13**. These are human derivations
and have **no new trust-zero Lean CI**.

**Next direct producer:** prove the true four-piece moving source functional bound in (B), or produce the real four-piece linearized PDE inverse with source norm strictly better than the absolute-integration threshold; do not spend another run proving shell-power identities or abstract packet termination.

**Public evidence retained:** finite spectral four-piece PDE telescope CI 42536552509 is strict Success, but is an exact identity only. Original revised acceptance remains **11/13**. The final Type-II strong orbit and its dynamically selected rate remain unproved.


## 6. New exact radial nonlocal derivative producer on a genuine outer annulus

The preceding Hilbert--Schmidt \(L^2(dr)\) estimate is for the *value*
of the original real Hessian Riesz term. Its spatial derivative can also
be controlled **without assuming a separate Riesz derivative envelope**,
provided the physical radial annulus starts at a stated positive radius.

Use the nonunitary Euclidean Fourier transform
\(\widehat f(\xi)=\int_{\mathbb R^3}e^{-ix\cdot\xi}f(x)\,dx\).
The Abel-regularized radial computation
\[
 \widehat{|x|^{-2}}(\xi)
  =\frac{4\pi}{|\xi|}
     \int_0^\infty\frac{\sin(|\xi|r)}r\,dr
  =\frac{2\pi^2}{|\xi|}
\]
is valid in tempered distributions. Since the bubble-normalized
coefficient is \(\kappa_{\rm H}=3/\pi^2\),
\[
 \widehat{\nabla\mathcal I f}(\xi)
   =6\,\frac{i\xi}{|\xi|}\widehat f(\xi).
\]
Plancherel therefore gives the **sharp full-vector multiplier
constant** (for \(f\in L^2(\mathbb R^3)\))
\[
 \boxed{\quad
 \|\nabla\mathcal I f\|_{L^2(\mathbb R^3)}
 =6\|f\|_{L^2(\mathbb R^3)}.
 \quad}
 \tag{R1}
\]
The equality is understood for the distributional gradient; it does not
claim that \(\mathcal I f\in L^2\). In particular the true Hartree
nonlocal derivative is an order-zero Riesz transform, **not**
a freely assumed derivative estimate.

For a radial scalar \(F\in L^2((0,\infty),dr)\),
\(f(x)=W(|x|)^3 F(|x|)\) satisfies
\[
 \frac{\|f\|_{L^2(\mathbb R^3)}}{\sqrt{4\pi}}
 =\|rW^3F\|_{L^2(dr)}
 \le\frac{2}{3\sqrt3}\|F\|_{L^2(dr)},
 \qquad
 \sup_{r>0}\frac r{(1+r^2)^{3/2}}
 =\frac2{3\sqrt3}.
\]
For every **explicit** \(R>0\), radial Plancherel and
\(r^2\ge R^2\) now imply
\[
 \boxed{\quad
 \|\partial_r\mathcal I(W^3F)\|_{L^2((R,\infty),dr)}
 \le\frac{4}{\sqrt3\,R}\|F\|_{L^2(dr)}.
 \quad}\tag{R2}
\]
There is no hidden dependence on a remote endpoint or spectral
Wronskian. The factor \(R^{-1}\) is displayed and is **not
discarded** in moving-small-radius regimes.

Moreover, for the exact nonlocal real-Hessian factor
\(N(F)=W^3\mathcal I(W^3F)\), use
\((W^3)'=-3r(1+r^2)^{-5/2}\),
\[
 \sup_{r>0}(1+r^2)W^3=1,\qquad
 \sup_{r>0}(1+r^2)|(W^3)'|=\frac2{\sqrt3}.
\]
The product rule, (R2), and the independent **proved paper**
Hilbert--Schmidt bound
\(\|\mathcal I(W^3F)\|_{L^2(dr)}\le3\|F\|_2\)
give
\[
 \boxed{
 \begin{aligned}
 \|(1+r^2)\partial_r N(F)\|_{L^2((R,\infty),dr)}
 &\le\left(\frac4{\sqrt3 R}+2\sqrt3\right)\|F\|_{L^2(dr)},\\
 \|(1+r^2)N(F)\|_{L^2((R,\infty),dr)}
 &\le3\|F\|_{L^2(dr)}.
 \end{aligned}
 }\tag{R3}
\]
All derivatives are interpreted weakly; the displayed estimates
extend by smooth radial approximation. The source in (R3) is exactly
the **true** \(W^3\mathcal I(W^3F)\) real-Hartree Hessian kernel,
not its local NLS replacement.

This closes the *paper* nonlocal-derivative estimate in the
\(r\ge R>0\) stationary bubble region, reducing that particular
component's weighted \(H^1\) budget to an explicit
\((1+R^{-1})\|F\|_{L^2(dr)}\). It does **NOT** control the
derivative of the whole time-moving quartic nonlinear residual
\(\mathcal N(V)\), since the latter involves the actual
four-region \(|V|^4\) density, its derivatives, nonlinear mixed
interactions and selected speeds. Nor does it establish any
Hartree matrix resolvent, adjoint Kato estimate or a PDE orbit.
For the *inner* \(R\downarrow0\) region, (R2)--(R3) have an explicit
unresolved \(R^{-1}\) loss; a stronger radial cancellation argument
would be needed before claiming radius-independent control there.
This calculation is not yet a Lean certificate.
**Official original acceptance stays 11/13.**
