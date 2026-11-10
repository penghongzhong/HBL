# HBL §2.13 — actual quartic Hartree quadratic remainder in the radial energy-dual source norm

**10 November 2026.** This is a new **paper proof** (not Lean verification), derived from the **same original physical Hartree potential**, not a separate nonlinear source hypothesis or a local quintic surrogate. The original revised theorem acceptance remains **11/13**. It uses the externally published weighted \(A_2\) Riesz theorem; this result is **not** inserted as a Lean axiom.

## 1. Exact nonlinear subtraction from the real Hartree bubble

Write
\[
\mathcal I f=\frac{3}{\pi^2}(|x|^{-2}*f),\quad
W(r)=(1+r^2)^{-1/2},\quad
Q(z)=|z|^2z,\quad
\mathcal N_{\rm H}(V)=\mathcal I(|V|^4)Q(V).
\]
For a smooth radial complex correction \(u=u_1+i u_2\), put
\(V=W+u\). The **actual** real-linear term at the bubble is
\[
\boxed{
 D\mathcal N_{\rm H}(W)u
 =9W^4u_1+3iW^4u_2
   +4W^3\mathcal I(W^3u_1).
}\tag{Q1}
\]
In particular its final term is genuinely nonlocal.

Define actual density and cubic Taylor pieces, **not freely chosen sources**,
\[
\begin{split}
 \rho_1&=4W^3u_1,\\
 \rho_2&=|W+u|^4-W^4-\rho_1\\
   &=2W^2|u|^2+4W^2u_1^2+4Wu_1|u|^2+|u|^4,\\
 Q_1&=W^2(u+2u_1),\\
 Q_2&=Q(W+u)-W^3-Q_1
    =W\bigl(|u|^2+2u_1u\bigr)+|u|^2u,\\
 P_W&=\mathcal I(W^4)=3W^2,\qquad
 P_1=\mathcal I(\rho_1),\qquad P_2=\mathcal I(\rho_2).
\end{split}\tag{Q2}
\]
The **full original** nonlinear remainder
\(\mathcal R_{\rm H}(u):=
\mathcal N_{\rm H}(W+u)-\mathcal N_{\rm H}(W)
-D\mathcal N_{\rm H}(W)u\) obeys the exact identity
\[
\boxed{\quad
 \mathcal R_{\rm H}(u)
 =P_W Q_2+P_1(Q_1+Q_2)+P_2Q(W+u).
 \quad}\tag{Q3}
\]
The existing strict Lean proof
\`actual_Hartree_complex_Taylor_polynomial_identity\` in
\`ActualHartreeComplexTaylor.lean\` already covers the **local polynomial**
identities underlying (Q2). It does not yet certify (Q3)'s full
integral/operator identity, or the weighted derivative estimate below.

## 2. Actual field-only norm control

Use the genuine correction norms
\[
 U=\|u\|_{L^2(dr)},\qquad
 H=\|(1+r^2)u'\|_{L^2(dr)},\qquad
 c=\frac{\sqrt\pi}{2},\qquad d=\sqrt{\frac\pi2},
\quad h=dH,\quad K=1+h.
\tag{Q4}
\]
The weighted one-dimensional fundamental theorem of calculus, with
\(u(\infty)=0\), gives
\[
 \|u\|_\infty\le cH,\qquad
 |u(r)|\le hW(r),\qquad |V(r)|\le KW(r).
\tag{Q5}
\]
No field \(L^\infty\), nonlocal potential, time exponent or bubble
velocity is an independent assumption.

The original fixed-weight radial \(A_2\) Riesz bound is
\[
 \|(\mathcal If)'\|_{L^2(dr)}
 \le6C_{A_2}\|f\|_{L^2(dr)},
\tag{Q6}
\]
where \(C_{A_2}<\infty\) is universal for
\(|x|^{-2}\in A_2(\mathbb R^3)\).
It follows from **T. P. Hytönen,** *The sharp weighted bound for general
Calderón--Zygmund operators*, **Annals of Mathematics 175** (2012),
1473--1506, DOI 10.4007/annals.2012.175.3.9.
This external theorem is a cited analytic ingredient, *not an extra
Lean axiom*. The source note
\`HBL_213_GLOBAL_RIESZ_A2_NO_INNER_RADIUS_LOSS_20261110.md\`
checks the required genuine **cube-based** \(A_2\) weight.

The elementary near/far \(3D\) inverse-square splitting gives
\(\|\mathcal If\|_\infty
\le\frac3{\pi^2}(4\pi\|f\|_\infty+\|f\|_{L^1(\mathbb R^3)})\).
Set the **derived**, nonnegative polynomials
\[
 A_1:=\frac{12}{\pi}
   (2\sqrt\pi H+\sqrt{3\pi}U),\qquad
 A_2:=\frac{72}{\pi}K^2(c^2H^2+U^2).
\tag{Q7}
\]
The true density decomposition (Q2) and (Q5) imply
\[
\begin{aligned}
&|\rho_2|\le6K^2W^2|u|^2,\\
&\|\rho_2\|_\infty\le6K^2c^2H^2,\qquad
\|\rho_2\|_{L^1(\mathbb R^3)}\le24\pi K^2U^2,\\
&\|\rho_2\|_{L^2(dr)}\le6K^2cHU,\\
&\|P_1\|_\infty\le A_1,\qquad
 \|P_1'\|_{L^2(dr)}\le24C_{A_2}U,\\
&\|P_2\|_\infty\le A_2,\qquad
 \|P_2'\|_{L^2(dr)}\le36C_{A_2}K^2cHU.
\end{aligned}\tag{Q8}
\]
For instance, the second line uses \(r^2W^2\le1\)
inside the **true** \(4\pi r^2dr\) density integral.
The \(P_1\) bound follows from
\(\int_0^\infty r^4W^6\,dr=3\pi/16\) and the
near/far split, so it contains **no invented Riesz envelope**.

## 3. Source and weighted source-gradient, explicitly quadratic

The genuine cubic algebra and (Q5) give
\[
\begin{aligned}
&\|Q_1\|_2\le3U,\qquad
 \|Q_2\|_2\le(3+h)cHU,\\
&\|(1+r^2)(Q_1+Q_2)\|_\infty
 \le3cH+(3+h)cdH^2,\\
&\|(1+r^2)Q_1'\|_2\le3(U+H),\\
&\|(1+r^2)Q_2'\|_2\le
 Z:=3cHU+6cH^2+3c^2H^3,\\
&\|(1+r^2)Q(V)\|_\infty\le K^3,\qquad
 \|(1+r^2)Q(V)'\|_2
       \le3K^2(\sqrt\pi/4+H).
\end{aligned}\tag{Q9}
\]
Indeed, differentiating \(Q_2=W(|u|^2+2u_1u)+|u|^2u\)
produces respectively
\(3|W'||u|^2\), \(6W|u||u'|\), \(3|u|^2|u'|\);
\((1+r^2)|W'|\le1\).
Also \(\|(1+r^2)(W^2)'\|_\infty\le1\).
There is **no nonintegrable weighted derivative of bare \(W\)**.

The exact quadratic identity (Q3), (Q8) and (Q9) now yield:
\[
\boxed{\begin{split}
 \|\mathcal R_{\rm H}(u)\|_{L^2(dr)}
 \le{}&
 3(3+h)cHU
 +A_1[3U+(3+h)cHU]\\
 &+A_2K^2(\sqrt{\pi/2}+U).
\end{split}}\tag{Q10}
\]
For the **full differentiated original nonlocal remainder**,
the product rule (weak derivatives are legitimate under the
displayed assumptions) gives
\[
\boxed{\begin{aligned}
 \|(1+r^2)\mathcal R_{\rm H}(u)'\|_{L^2(dr)}
 \le{}&
 3(3+h)cHU+3Z\\
 &+24C_{A_2}U[3cH+(3+h)cdH^2]\\
 &+A_1[3(U+H)+Z]\\
 &+36C_{A_2}K^5cHU\\
 &+3A_2K^2(\sqrt\pi/4+H).
\end{aligned}}\tag{Q11}
\]
Every summand on the right contains **at least two actual
factors** from the correction norms \(U,H\).
The term \(36C_{A_2}K^5cHU\) is the
\(P_2'Q(V)\) contribution of the full nonlocal density;
its absence would be an invalid local-NLS simplification.

In particular, for \(0\le U,H\le1\), there is a completely
universal \(C_{\rm H}=C(C_{A_2})<\infty\) such that
\[
\boxed{
 \|\mathcal R_{\rm H}(u)\|_2
 +\|(1+r^2)\mathcal R_{\rm H}(u)'\|_2
 \le C_{\rm H}(U+H)^2.
}\tag{Q12}
\]
This is **not** the false claim that the full PDE
residual is quadratic: the exact linearized Hartree
term (Q1), the moving transport, local Laplacian,
two-source Kummer mismatch, Cramer/Volterra time terms
and radiation error all remain.

## 4. Genuine critical-scale covariance without a prescribed rate

For \(\lambda>0\), put
\(W_\lambda(r)=\lambda^{-1/2}W(r/\lambda)\) and
\(u_\lambda(r)=\lambda^{-1/2}u(r/\lambda)\).
The original physical cubic-quartic Hartree nonlinearity,
including its convolution, has the exact scaling
\(\mathcal N_{\rm H}(W_\lambda+u_\lambda)(\lambda r)
=\lambda^{-5/2}\mathcal N_{\rm H}(W+u)(r)\).
The real-linear term scales identically, so
\[
\begin{aligned}
\|\mathcal R_{{\rm H},\lambda}(u_\lambda)\|_{L^2(dr)}
  &=\lambda^{-2}\|\mathcal R_{\rm H}(u)\|_{L^2(dr)},\\
\|(\lambda^2+r^2)\partial_r
   \mathcal R_{{\rm H},\lambda}(u_\lambda)\|_{L^2(dr)}
  &=\lambda^{-1}\|(1+r^2)\mathcal R_{\rm H}(u)'\|_{L^2(dr)}.
\end{aligned}\tag{Q13}
\]
No \(\lambda(s)\) or Type-II speed has been assumed.

**What this removes:** the *fully nonlinear* Hartree
source remainder is quadratically controlled in the
spatial \(H^1\) dual-source topology solely by the true
radial field norms and an established Riesz theorem.
The rate is not inserted.

**What remains genuinely open:** rigorous smallness and
parameter-Lipschitz control of \(U(s),H(s)\) on the *same
moving four-piece field*, all linear/moving/local PDE
residual terms, the coupled Hartree nonresonant
Kato/resolvent bound in matching spaces, construction of
the actual orbit and derivation of the Type-II rate.
The weighted \(A_2\) theorem is not yet a Lean import;
this new *paper* proof has **no strict Lean CI**.
Original **11/13**.
