# HBL §2.13 — genuine nonlocal Hessian derivative with **no inner-radius loss**

**10 November 2026 — paper proof only, not a Lean theorem. Original revised acceptance remains 11/13.** This calculation corrects a previously nonsharp radius-dependent intermediate estimate for the *fixed ground-state Hartree real Hessian*. It does **not** claim a full nonlinear four-region PDE residual derivative, an adjoint Kato theorem, a Hartree orbit, or Type-II dynamics.

## 1. Exact physical operator and the weighted Riesz-transform reduction

The original three-dimensional inverse-square Hartree potential is
\[
 \mathcal I f=\kappa_{\rm H}(|x|^{-2}*f),
 \qquad \kappa_{\rm H}=3/\pi^2,
 \qquad W(r)=(1+r^2)^{-1/2}.
\]
In the nonunitary Fourier convention
\(\widehat f(\xi)=\int_{\mathbb R^3}e^{-ix\cdot\xi}f(x)\,dx\),
\[
 \widehat{|x|^{-2}}(\xi)=2\pi^2|\xi|^{-1},
 \qquad
 \widehat{\nabla\mathcal I f}(\xi)
     =6i\frac{\xi}{|\xi|}\widehat f(\xi).
 \tag{A1}
\]
Thus the exact physical nonlocal derivative is six times the
vector of Riesz transforms \(\mathcal R=\nabla(-\Delta)^{-1/2}\).

Take the **fixed, explicit** weight
\[
 \omega(x)=|x|^{-2},\qquad x\in\mathbb R^3.
\]
This is genuinely an \(A_2\) Muckenhoupt weight in
dimension \(3\): the classical power criterion
\(|x|^\alpha\in A_2(\mathbb R^3)\iff -3<\alpha<3\)
applies with \(\alpha=-2\).
For completeness, the ball \(A_2\) bound can be
verified without an external assumption:
if \(|c|\ge2R\), then
\[
 \left(\fint_{B(c,R)}\omega\right)
 \left(\fint_{B(c,R)}\omega^{-1}\right)\le9;
\]
if \(|c|<2R\), use
\(B(c,R)\subset B(0,3R)\) to obtain
\[
 \fint_{B(c,R)}\omega\le9R^{-2},\qquad
 \fint_{B(c,R)}\omega^{-1}\le9R^2,
\]
so the product is at most \(81\).
The ball and cube definitions of \(A_2\) are equivalent
up to a dimension-only constant; in particular
\([\omega]_{A_2}<\infty\).

The published **weighted Calderón–Zygmund \(A_2\) theorem**
(T. P. Hytönen, *The sharp weighted bound for general
Calderón–Zygmund operators*, *Annals of Mathematics*
**175** (2012), 1473–1506,
DOI **10.4007/annals.2012.175.3.9**)
applies to each three-dimensional Riesz transform.
Consequently there is a fixed finite
\(C_\omega\) (including the vector's finite-dimensional
norm) such that
\[
 \boxed{
 \bigl\||x|^{-1}\mathcal R f\bigr\|_{L^2(\mathbb R^3)}
 \le C_\omega
   \bigl\||x|^{-1}f\bigr\|_{L^2(\mathbb R^3)}.
 }
 \tag{A2}
\]
**Crucial:** \(C_\omega\) is independent of every inner
radius \(r_0\), outer radius \(B\), moving Kummer scale,
source \(F\), and observation annulus. It is not a new
postulated physical source envelope: (A2) is a published
general operator theorem applied to the explicit genuine
Hartree Fourier multiplier and an explicitly verified
\(A_2\) weight.

## 2. The exact \(dr\) radial measure, not \(r^2dr\)

Let \(F\in L^2((0,\infty),dr)\) be radial and set
\(f(x)=W(|x|)^3F(|x|)\). Radial integration gives
\[
 \bigl\||x|^{-1}f\bigr\|_{L^2(\mathbb R^3)}
    =\sqrt{4\pi}\,\|W^3F\|_{L^2(dr)},
\]
and, because \(\mathcal I f\) is radial,
\[
 \bigl\||x|^{-1}\nabla\mathcal I f
    \bigr\|_{L^2(\mathbb R^3)}
    =\sqrt{4\pi}\,
       \bigl\|\partial_r\mathcal I(W^3F)
         \bigr\|_{L^2(dr)}.
\]
Combining these with (A1)–(A2) produces the
**global, origin-uniform derivative bound**
\[
 \boxed{
 \|\partial_r\mathcal I(W^3F)\|_{L^2(dr)}
 \le 6C_\omega\|W^3F\|_{L^2(dr)}
 \le 6C_\omega\|F\|_{L^2(dr)} .
 }
 \tag{A3}
\]
The derivative is interpreted weakly, and approximation
extends the estimate from smooth radial \(F\) to the
stated \(L^2(dr)\) source class. There is **no** \(r_0^{-1}\)
factor, even as \(r_0\downarrow0\). This is strictly
stronger than the earlier bound
\(\|\partial_r\mathcal I(W^3F)\|_{L^2((R,\infty),dr)}
\le4(\sqrt3R)^{-1}\|F\|_2\),
which remains true but is nonsharp near \(R=0\).

## 3. Complete fixed-bubble nonlocal Hessian weighted \(H^1\) gain

The same exact physical nonlocal real-Hessian term is
\[
 N(F)(r)=W(r)^3\mathcal I(W^3F)(r).
\]
The independent, previously computed
Hilbert–Schmidt bound in the **same** \(dr\) measure is
\[
 \|\mathcal I(W^3F)\|_{L^2(dr)}
   \le3\|F\|_{L^2(dr)}.
\]
The two explicit multiplication weights obey
\[
 \|(1+r^2)W^3\|_{L^\infty}\le1,\qquad
 \|(1+r^2)(W^3)'\|_{L^\infty}\le\frac2{\sqrt3}.
\]
The distributional product rule and (A3) therefore yield
\[
 \boxed{
 \begin{aligned}
 \|(1+r^2)N(F)\|_{L^2(dr)}
    &\le3\|F\|_{L^2(dr)},\\
 \|(1+r^2)N(F)'\|_{L^2(dr)}
    &\le\underbrace{(6C_\omega+2\sqrt3)}_{C_{\rm H}}
       \|F\|_{L^2(dr)}.
 \end{aligned}
 }
 \tag{A4}
\]
In particular the true nonlocal fixed-bubble Hessian
\(\,F\mapsto W^3\mathcal I(W^3F)\,\)
maps \(L^2(dr)\) into the physical weighted radial
\(H^1\)-type norm **without any artificial left-radius loss**.
No NLS local-potential surrogate is used.

## 4. Equivalent self-contained Mellin reduction (for eventual direct formalization)

The original radial angular integral is
\[
 \mathcal I(W^3F)(r)
 =2\pi\kappa_{\rm H}\int_0^\infty
    \frac{s}{r}\log\frac{r+s}{|r-s|}
    W(s)^3F(s)\,ds .
\]
Differentiation in the principal-value distributional sense
produces the homogeneous kernel
\[
 \partial_r\left[
 \frac{s}{r}\log\frac{r+s}{|r-s|}\right]
  =r^{-1}\Phi(s/r),\quad
 \Phi(t)=\frac{2t^2}{t^2-1}
       -t\log\frac{1+t}{|1-t|}.
\]
The unitary Mellin map
\((Uf)(x)=e^{x/2}f(e^x)\)
from \(L^2(dr)\) to \(L^2(dx)\)
conjugates the radial derivative into principal-value
convolution on \(\mathbb R\) with
\[
 k(u)=e^{u/2}\Phi(e^u)
 =e^{3u/2}\left[
     (\sinh u)^{-1}
      -\log|\coth(u/2)|
   \right].
\]
Direct Taylor expansions give
\[
 k(u)-\mathbf1_{|u|<1}\frac1u\in L^1(\mathbb R);
\]
indeed \(k(u)=u^{-1}+O(1+|\log|u||)\)
as \(u\to0\), while
\(k(u)=O(e^{-3u/2})\) as \(u\to+\infty\)
and \(k(u)=O(e^{5u/2})\) as \(u\to-\infty\).
The truncated Hilbert transform
\(\mathrm{p.v.}\int_{|u|<1}h(x+u)\,du/u\)
has bounded Fourier multiplier
\(2i\int_0^\xi\sin t\,dt/t\).
Young's inequality then independently proves
boundedness of this genuine radial derivative
on \(L^2(dr)\). This supplies a direct one-dimensional
alternative if the global weighted \(A_2\) theorem
is inconvenient to formalize in Lean.

The Mellin and \(A_2\) methods agree on the key
mathematical point: **the previously visible \(R^{-1}\)
was caused by discarding radial cancellation and
moving a factor \(r^{-1}\) outside the full
three-dimensional transform; it is not an intrinsic
loss of the physical nonlocal Hartree Hessian.**

## 5. Exact acceptance boundary

This step *closes a genuine paper-level fixed-bubble
nonlocal-derivative gap*, not the original complete
four-region physical PDE source estimate.

The physical residual still contains
\(\mathcal I(|V|^4)\,|V|^2V\) for a time-moving
\(V\), true mixed Riesz density terms,
moving first/second/third interface derivatives
and the modulation time drift. These cannot be
replaced by the linear fixed-bubble Hessian
\(N(F)\). The source's **own** spatial derivative,
\(C^2\) real interface matching,
parameter-Lipschitz estimate and the full coupled
Hartree projected adjoint smoothing/energy inverse
are still OPEN. This published harmonic-analysis
input is **cited in the paper** but
**not yet implemented as a Lean lemma or axiom**;
strict Lean axioms remain only
\`propext\`, \`Classical.choice\`, \`Quot.sound\`.
Neither revised original §2.13 nor the Type-II
main theorem is thereby accepted; **11/13**.
