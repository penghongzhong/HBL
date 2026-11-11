# HBL §2.13: C¹ Green cancellation for merely integrable forcing and a weak backward overlap

11 November 2026. **New paper-level argument, not a Lean strict acceptance.** The aim is to replace two unnecessarily strong intermediate interfaces: (i) forcing continuity in the source-to-three-C¹-join chain, and (ii) third spatial traces of a moving C³ Hermite shell. Both replacements preserve the *actual* Hartree source. They do **not** furnish a time-positive nonlinear residual, a finite recursion, or a dynamically selected blow-up rate.

## 1. The original Green formula gains one derivative by exact Wronskian cancellation

Fix a compact interval \([a,b]\Subset(0,R_K)\), and let \(F:\,(0,R_K)\to\mathbb C\) be locally Lebesgue integrable. Suppose \(X,Y\in C^2((0,R_K);\mathbb C)\), their Wronskian \(W=XY'-X'Y\) is nowhere zero, and the two Green densities
\[
h_X(t)=X(t)F(t)/W(t),\qquad h_Y(t)=Y(t)F(t)/W(t)
\]
are locally integrable. Define the **unswapped original** coefficients
\[
A(r)=\int_r^b h_X(t)\,dt,\qquad B(r)=\int_a^r h_Y(t)\,dt,
\qquad u(r)=Y(r)A(r)+X(r)(B(r)+\gamma).
\tag{WG1}
\]
For almost every \(r\), \(A'=-XF/W\), \(B'=YF/W\). Their absolutely continuous representatives satisfy
\[
\begin{aligned}
u'_{\mathrm{a.e.}}(r)
 &=Y'(r)A(r)+X'(r)(B(r)+\gamma)
   +Y(r)A'(r)+X(r)B'(r)\\
 &=Y'(r)A(r)+X'(r)(B(r)+\gamma)
  =:H(r).
\end{aligned}\tag{WG2}
\]
The singular *derivative-of-integral* terms cancel **exactly**, with no continuity assumption on \(F\). Since \(A,B\) are absolutely continuous, \(H\) is continuous. For any \(r_1,r_2\) in the positive interval,
\[
u(r_2)-u(r_1)=\int_{r_1}^{r_2}H(t)\,dt.
\tag{WG3}
\]
Thus \(u\in C^1\) and \(u'=H\) **at every positive radius**, including the endpoints if the original forcing is locally integrable on an open neighborhood of them. This establishes the *mathematical* C¹ Green bridge from interval integrability; the existing Lean theorem still asks for \`ContinuousAt F\` and has **not** yet been replaced by a compiled weaker statement.

Moreover \(H\) is absolutely continuous and, almost everywhere,
\[
u''(r)=Y''(r)A(r)+X''(r)(B(r)+\gamma)
+\frac{X'(r)Y(r)-Y'(r)X(r)}{W(r)}F(r).
\tag{WG4}
\]
For the stated Wronskian convention, the last term is \(-F(r)\). This is the *actual* a.e. Kummer second-order equation, with its coefficient signs inherited from the original basis. No everywhere-classical second derivative is asserted.

In particular, the measurable Hartree step-source counterexample previously constructed does **not** obstruct C¹ Green matching: its forcing jumps, but (WG2) stays continuous. It obstructs *classical C² at the jump*. The previous conclusion that the existing theorem types cannot be directly composed remains correct; the new observation is that a shorter theorem with a weaker and physically available source premise is mathematically valid.

For the corrected spectral field
\[
u_{\rm corr}=u-\mathcal G_{a,b}[d\,u;0,0],
\tag{WG5}
\]
\(u\in C^1\), so \(d\,u\) is continuous (hence locally integrable). The second zero-left Green solve is C¹ by the same argument, and preserves the exact left Cauchy pair. Consequently **all three C¹ joins can be formulated without continuity of the original Hartree forcing** provided the actual Fredholm left traces, endpoint identities and outer repair are imported. The resulting classical \(C^1\) statement is a pending Lean replacement of the current continuity-dependent theorem; the full corrected PDE identity still holds only a.e. at the level of source regularity.

## 2. The original backward-overlap geometry removes the C³-jet premise

Let \(L>0\), \(I_L=[5L/8,L]\), and suppose the true inner Fredholm field \(u\) and the matched corrected Kummer continuation \(v\) are in \(W^{2,2}(I_L)\), with **genuine** left Cauchy matching at \(r=L\):
\[
f=u-v,\quad f(L)=f'(L)=0,\qquad
g(r)=\Delta_r f(r):=f''(r)+\frac2r f'(r)\in L^2(I_L,r^2\,dr).
\tag{WG6}
\]
Here \(g\) is the *computed difference of the two original spatial differential operators*, not an independently postulated small forcing. The radial flux identity is
\[
(r^2 f')'=r^2 g,\qquad
f'(r)=-r^{-2}\int_r^L t^2g(t)\,dt,\qquad
f(r)=-\int_r^L f'(t)\,dt.
\tag{WG7}
\]
Write \(\|h\|_{r,2}=(\int_{5L/8}^L r^2|h(r)|^2\,dr)^{1/2}\). The Volterra operator \(Th(r)=\int_r^L h(t)\,dt\) obeys \(\|Th\|_{L^2}\le (3L/8)\|h\|_{L^2}\). Since \(t/r\le8/5\) and \(r/t\le1\) for \(r\le t\le L\), (WG7) gives
\[
\boxed{\quad
 \|f'\|_{r,2}\le \frac{3L}{5}\|g\|_{r,2},
 \qquad
 \|f\|_{r,2}\le \frac{9L^2}{40}\|g\|_{r,2}.
 \quad}
\tag{WG8}
\]
No inverse power of the moving left radius occurs.

Use precisely the backward transition already defined in
\`ActualHartreeSameSourceBackwardFlatOverlap.lean\`:
\[
\eta_L(r)=\chi(8r/L-4).
\tag{WG9}
\]
Its derivative is supported in \([5L/8,3L/4]\). Let \(A=\|\chi'\|_\infty\), \(B=\|\chi''\|_\infty\). Define the local interpolant
\[
U(s,r)=u(s,r)-\eta_{L(s)}(r)\,[u(s,r)-v(s,r)]\,=\,(1-\eta_L)u+\eta_Lv.
\tag{WG10}
\]
Then
\[
\Delta_r U-(1-\eta_L)\Delta_rv-\eta_L\Delta_ru
=-2\eta_L'f'-(\eta_L''+2\eta_L'/r)f.
\tag{WG11}
\]
Using \(|\eta_L'|\le8A/L\), \(|\eta_L''|\le64B/L^2\), \(2/r\le16/(5L)\), and (WG8), one obtains the explicit **strong source** estimate
\[
\boxed{\quad
\|\Delta_r U-(1-\eta_L)\Delta_ru-\eta_L\Delta_rv\|_{r,2}
\le\left(\frac{384}{25}A+\frac{72}{5}B\right)\|g\|_{r,2}.
\quad}
\tag{WG12}
\]

If \(L\in C^1\), differentiation at fixed physical radius gives
\[
\partial_s\eta_L(r)
=-\chi'(8r/L-4)\frac{8rL'}{L^2}.
\tag{WG13}
\]
On the support of \(\chi'\), \(r\le3L/4\). Therefore
\[
\boxed{\quad
\|(\partial_s\eta_L+b\,r\partial_r\eta_L)f\|_{r,2}
\le\frac{27A}{20}\bigl(L|L'|+L^2|b|\bigr)\|g\|_{r,2}.
\quad}
\tag{WG14}
\]
These are **genuine moving-interface bounds** for the already coded overlap, based on the *actual spatial equation difference*. They require neither third spatial traces nor time differentiation of a piecewise Laplacian; the moving-interface delta terms never arise because the interpolation is smooth.

## 3. Exact Hartree PDE identity and its remaining nonlocal term

Write the original renormalized operator (with the precise project sign convention)
\[
\mathscr R_{b,\omega}(q)
=i q_s+\Delta_rq+\mathcal N_H(q)
+i b(\tfrac12q+r q_r)+\omega q.
\tag{WG15}
\]
For the true global interpolated field \(U\), its restriction to \(I_L\) satisfies, as a strong a.e. identity,
\[
\begin{aligned}
\mathscr R_{b,\omega}(U)
={}&(1-\eta_L)\mathscr R_{b,\omega}(u)
+\eta_L\mathscr R_{b,\omega}(v)\\
&-2\eta_L'f'-(\eta_L''+2\eta_L'/r)f
-i(\partial_s\eta_L+b r\eta_L')f\\
&+\Bigl\{
\mathcal N_H(U)-(1-\eta_L)\mathcal N_H(u)
-\eta_L\mathcal N_H(v)\Bigr\}.
\end{aligned}\tag{WG16}
\]
The braces are the **full nonlocal inverse-square quartic Hartree interaction** computed from the complete three-dimensional fields, not a local cubic surrogate; they are not controlled by (WG12). The identity is valid only after specifying the actual globally defined interpolated packet and its true nonlocal potentials.

This route replaces the *C³ Hermite repair* as a proposed intermediate construction. It does **not** replace either original unproved environment, because the still-needed inputs are:
(a) a weak \(W^{2,2}\) extension of the **same corrected** Green solution to the backward annulus \([5L/8,L]\), derived from the actual original source;
(b) control of the actual \(\|g\|_{r,2}\), including the moving basis/speeds, from the same PDE orbit;
(c) the complete nonlocal defect in braces in the correct global source norm;
(d) a time-weighted and parameter-Lipschitz bootstrap closing the finite recursion; and
(e) a PDE-derived Type-II rate.

The existing strict [four-piece telescoping CI 42958494409](https://github.com/penghongzhong/HBL/actions/runs/42958494409) proves an exact algebraic identity but **not** any of (a)–(e). This paper-level change makes the shortest route mathematically less regularity-demanding and eliminates a spurious \(\|(\partial_s\Delta P)_{\rm reg}\|_2\sim h^{-1/2}\) obstruction from the discarded C³ approach. It does not assert time gain from (WG12) alone.

**Formal original-paper acceptance remains 11/13 (84.62%). No new strict Lean CI in this note.**