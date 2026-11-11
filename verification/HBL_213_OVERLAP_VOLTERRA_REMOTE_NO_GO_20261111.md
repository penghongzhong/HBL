# HBL §2.13: finite-energy overlap splice without a third source jet; an actual remote-Hartree counterexample

11 November 2026 (UTC). This document is a **paper proof and acceptance-boundary audit**, not a newly compiled Lean declaration or a solved original §2.13. Formal revised original environments remain **11/13**.

## 1. A radius-uniform, source-derived overlap splice

Take an actual positive physical interface radius \(L>0\), width \(0<h\le L\), and \(I=[L,L+h]\). Suppose that the two **existing actual inner/Fredholm and outer/Kummer physical fields** \(u,v:I\to\mathbb C\) admit \(W^{2,2}\) representatives (classical one-sided fields suffice), and that their *already verified* matching data at the same interface are
\[
 D(L)=D'(L)=0,\qquad D=u-v.
\]
No third derivative or curvature trace is required. Set
\[
 E(r)=\Delta_r u(r)-\Delta_r v(r)
       =D''(r)+2r^{-1}D'(r),\quad
 A=\bigg(\int_L^{L+h}r^2|E(r)|^2\,dr\bigg)^{1/2}<\infty.
\]
Here \(E\) is **defined by the actual two fields**; its smallness is not postulated. The exact radial Wronskian/Volterra equation is
\[
 (r^2D')'=r^2 E,\qquad
 D'(r)=r^{-2}\int_L^r \rho^2E(\rho)\,d\rho .
\]
Cauchy--Schwarz and \(L\le r,\rho\le L+h\le 2L\) imply
\[
 |D'(r)|\le {2\sqrt h\over L}A,\qquad
 |D(r)|\le {2h^{3/2}\over L}A.
\]
Writing \(\|\cdot\|_{2,r^2}=\|\cdot\|_{L^2(I;r^2dr)}\), integration yields
\[
 \boxed{\ \|D'\|_{2,r^2}\le4hA,\qquad
         \|D\|_{2,r^2}\le4h^2 A.\ }\tag{OS1}
\]
No hidden inverse power of the left radius remains.

Choose a fixed smooth real cutoff \(\chi_0\), equal to one near \(0\) and zero near \(1\), \(0\le\chi_0\le1\), with \(|\chi_0'|\le C_1\), \(|\chi_0''|\le C_2\). Put
\[
 \chi_{L,h}(r)=\chi_0((r-L)/h),\qquad
 P(r)=\begin{cases}\chi_{L,h}(r)D(r),&r\in I,\\0,&r\notin I.\end{cases}
\]
Define the repaired field to be \(u\) left of \(L\), \(v+P\) in \(I\), and \(v\) right of \(L+h\). It agrees with \(u\) near \(L\) and with \(v\) near \(L+h\), so it has the same within-piece \(W^{2,2}\) spatial regularity without ever evaluating \(u'''(L)\) or \(v'''(L)\). The correction \(P\) itself is only \(C^1\) across \(L\) when the original second-jet jump is nonzero; its Laplacian jump precisely cancels that of the old sharp field. Do NOT describe \(P\) as globally \(C^2\).

Within \(I\), the exact physical radial equation reads
\[
 \Delta_rP=\chi_{L,h} E+
 2\chi_{L,h}'D'+(\chi_{L,h}''+2r^{-1}\chi_{L,h}')D.
\tag{OS2}
\]
From (OS1),
\[
\begin{split}
 \|P\|_{2,r^2}&\le4h^2A,\\
 \|P'\|_{2,r^2}&\le4(1+C_1)hA,\\
 \boxed{\ \|\Delta_rP\|_{2,r^2}
 &\le(1+16C_1+4C_2)A.\ }\tag{OS3}
\end{split}
\]
Indeed the terms in (OS2) are bounded by \(A\), \(8C_1A\), \(4C_2A\), and \(8C_1(h/L)A\), respectively. This is an **actual-difference-source stability identity**: \(A\) must still be bounded from the same original Hartree two-channel and Kummer equations on the overlap. Merely knowing one endpoint curvature jump does not bound \(A\).

For the global radial zero-extension of \(P\), the physical three-dimensional energy obeys
\[
 \boxed{\ \|\nabla P\|_{L^2(\mathbb R^3)}
 \le4\sqrt{4\pi}(1+C_1)h A.\ }\tag{OS4}
\]
Consequently the *entire* original inverse-square quartic Hartree nonlinearity
\[
 {\cal N}_H(U)=\kappa_H (|x|^{-2}*|U|^4)|U|^2U
\]
has the genuine, nonlocal energy-dual perturbation bound
\[
 \boxed{\ \|{\cal N}_H(U+P)-{\cal N}_H(U)\|_{\dot H^{-1}}
 \le C_H(\|\nabla U\|_2+\|\nabla P\|_2)^6\,\|\nabla P\|_2.\ }\tag{OS5}
\]
The constant depends only on the fixed Hartree normalization and Sobolev/HLS constants. Proof: expand the degree-four density and degree-three multiplier in multilinear form; apply Hardy--Littlewood--Sobolev to the double integral with kernel \(|x-y|^{-2}\) and Sobolev \(\|f\|_6\lesssim\|\nabla f\|_2\). This does NOT assert control in the stronger Hessian--Morawetz dual used in the previous route, nor does it imply that previously selected speeds remain compatible: the entire new Hartree convolution must be inserted into the Cramer equations.

## 2. The moving-interface term is explicit, not suppressed

For time-dependent \(L(s),h(s),D(s,r)\), differentiating the smooth overlap cutoff at fixed physical \(r\) gives
\[
 \partial_s\chi_{L,h}(r)
 =-\chi_0'((r-L)/h)\bigl(L_s/h+(r-L)h_s/h^2\bigr).
\]
Thus
\[
 P_s=\chi_{L,h}D_s+(\partial_s\chi_{L,h})D,\qquad
 \|(\partial_s\chi_{L,h})D\|_{2,r^2}
 \le 4C_1h(|L_s|+|h_s|)A.\tag{OS6}
\]
The renormalized spatial scaling term also has the exact extra commutator \(i\,b r\chi_{L,h}'D\), bounded in the annulus by \(8C_1|b|LhA\). But neither \(\chi D_s\) nor \(L_s,h_s\) are controlled by (OS1)--(OS5). If \(E\) has a one-sided trace and the matching holds differentiably in \(s\), differentiation of \(D'(s,L(s))=0\) gives
\[
 D_s'(s,L(s))=-L_s(s)E(s,L(s)),
\]
since \(E(L)=D''(L)\). This is a *source-derived* moving boundary term and not zero in general.

**Acceptance gate:** produce \(A(s)\) and the time/parameter bounds of \(D_s,L_s,h_s\) from the **same four-piece nonlocal Hartree PDE**, show a positive time power in the full residual of the *repaired* field, and recompute the two real compatibility speeds. No independent time envelope or assumed blowup rate is introduced by this overlap construction. The \(L^2/\dot H^{-1}\) route also needs a genuine evolution/stability theorem in that topology: it does not automatically validate the original stronger Kato/Hessian dual.

## 3. A genuine smooth-radiation counterexample to globalizing the half-power source bound

The newly verified \(\ell^{1/2}\) ten-term source estimate holds on \(0<r\le2L\), \(L=\ell^{-1/16}\). It cannot be extended to all remote radii at the **same** \((1+r)^{-4}\) spatial weight using only its existing amplitude/Strauss hypotheses, even for smooth compact radiation.

Take \(c=0\), the actual real core \(V(r)=W(r)=(1+r^2)^{-1/2}\), and choose a nonnegative real \(z\in C_c^\infty((1/2,5/2))\) with \(z=1\) on \([1,2]\). This \(z\) satisfies the same global boundedness and radial Strauss hypotheses with constants independent of \(\ell\). Let \(Z_\ell(r)=\sqrt\ell\,z(\ell r)\), \(r_\ell=\ell^{-1}\), \(0<\ell\le1\). Then
\[
 V(r_\ell)=\frac{\ell}{\sqrt{1+\ell^2}}\ge\ell/2,\qquad
 Z_\ell(r_\ell)=\sqrt\ell .
\]
The *actual* radial Hartree quartic self-radiation potential is
\[
 P_Z(r)=\frac{2\pi\kappa_H}{r}
       \int_0^\infty \rho
       \log\frac{r+\rho}{|r-\rho|}\,|Z_\ell(\rho)|^4\,d\rho.
\]
On \(\rho\in[(6/5)/\ell,(13/10)/\ell]\) the logarithm exceeds one and \(z(\ell\rho)=1\), so
\[
 P_Z(r_\ell)\ge2\pi\kappa_H\ell\cdot
 \ell^2\int_{(6/5)/\ell}^{(13/10)/\ell}\rho\,d\rho
 =\frac{\pi\kappa_H}{4}\ell.
\]
All three terms in the *original* interaction
\({\cal S}_H={\cal N}_H(V+Z)-{\cal N}_H(V)-{\cal N}_H(Z)\) are nonnegative for these real nonnegative fields; in particular the true pure-radiation-potential/cubic-difference contribution is
\[
 {\cal S}_H(r_\ell)\ge P_Z(r_\ell)
 [(V(r_\ell)+Z_\ell(r_\ell))^3-Z_\ell(r_\ell)^3]
 \ge 3P_Z(r_\ell)V(r_\ell)Z_\ell(r_\ell)^2
 \ge\frac{3\pi\kappa_H}{8}\ell^3.
\tag{OS7}
\]
Hence
\[
 (1+r_\ell)^4|{\cal S}_H(r_\ell)|
 \ge\frac{3\pi\kappa_H}{8}\ell^{-1},
\]
which **cannot** be bounded by \(K(B,A)\ell^{1/2}\) with a scale-independent \(K\). The same example rules out a global weighted conjugated bound of the slow-inner form. It does not disprove the previously strict *weaker full-annulus* \(\ell^{1/8}\) bound, or exclude a more favorable estimate on a particular shorter Cramer interval not reaching \(r\asymp\ell^{-1}\).

This counterexample proves that moving the strict slow-inner \(\ell^{1/2}\) bound into the entire selected outer Cramer source is mathematically invalid without **additional far-field cancellation or localization**. The outer contribution must remain independently accounted for in the same PDE.

## Formal scope

Previously strict original \(C^1\) and native \(C^2\) interface identities remain valid. Strict runs [42954150551](https://github.com/penghongzhong/HBL/actions/runs/42954150551) and [42954150615](https://github.com/penghongzhong/HBL/actions/runs/42954150615) prove, respectively, the exact slow-inner weighted squared integral and three original source pointwise declarations, under the pinned Lean/Mathlib toolchain, trust-zero and allowed three-axiom audits. **Neither (OS1)--(OS7) nor a full physical trajectory has been Lean-certified in this note.** The original finite PDE telescope is still an equality (strict [42927397872](https://github.com/penghongzhong/HBL/actions/runs/42927397872)), not a positive time-power estimate. Revised numbered acceptance remains **11/13**. 


## 4. A source-faithful absorption estimate for the actual frozen Kummer mismatch

This refines (OS1)--(OS3) without **assuming** the size of \(E\). On any overlap where both genuine inner and spectral outer fields solve their stated equations, let \(a>0\), \(c_0=\mathrm{frozenZeroCoeff}(\mu,\theta)\in\mathbb C\), and use the *actual* scaled Kummer operator from \`ActualHartreeMatchedKummerShellGain.lean\`:
\[
 {\cal K}_a f=\Delta_r f+a^{-2}\bigl(\tfrac{i r}{2}f'+c_0f\bigr).
\]
Let \(\mathcal S_H\) denote the **same** original quartic nonlocal Hartree source evaluated for the full physical field (not separately postulated inner and outer sources). Let \(u_0\) be the selected source-normalized Green field and \(d\) the spectral correction parameter, and define the actual equation defects on \(I\) by
\[
 T={\cal K}_a u+\mathcal S_H,\qquad
 O={\cal K}_a v+\mathcal S_H+a^{-2}d\,u_0.
\]
The second defect vanishes if the original source-to-Kummer scaling identity and selected spectral outer equation hold **throughout this overlap**; this is not inferred from a single endpoint identity. Subtracting these two literal equations gives
\[
 E=\Delta_r(u-v)
   =T-O+a^{-2}d\,u_0
    -a^{-2}\bigl(\tfrac{i r}{2}D'+c_0D\bigr).
\tag{OS8}
\]
Consequently, setting
\[
 B=\|T\|_{2,r^2}+\|O\|_{2,r^2}
       +a^{-2}|d|\,\|u_0\|_{2,r^2},\quad
 \Theta=\frac{4Lh+4|c_0|h^2}{a^2},
\]
the *proven* zero-jet Volterra bounds (OS1) imply
\[
 A\le B+\Theta A,\qquad
 \boxed{\ \text{if }\Theta\le\tfrac12,\quad
 A\le2B,\quad
 \|\nabla P\|_2\le8\sqrt{4\pi}(1+C_1)hB.\ }\tag{OS9}
\]
No smallness of \(A\) and no extra third-jet hypothesis has been inserted: \(A\) is **absorbed** against the fixed operator's true first-/zero-order term. This is the exact place where the original source and its corrected spectral shift can be reused.

For example, moving the normalized match to the left edge \(L_0=L_{\mathrm{slow}}/2\) of the *already estimated* backward overlap \([L_{\mathrm{slow}}/2,L_{\mathrm{slow}}]\), with \(h=L_0\), gives \(\Theta=(1+|c_0|)L_{\mathrm{slow}}^2/a^2\). This is small when the actual geometric and Kummer parameters satisfy the displayed explicit inequality; it is **not** claimed unconditionally. This re-anchoring requires reconstructing the genuine selected two-channel matching data at \(L_0\) and ensuring the outer Kummer source equation holds on the full chosen interval. Neither step follows from the existing \(C^1\) theorem at \(L_{\mathrm{slow}}\).

The remaining true analytic inputs are now visible and non-circular: derive the two actual defects \(T,O\) on one common overlap from the existing original Hartree source/Green laws, control \(B\) with the *correct original outer annulus* (not with the restricted half-power bound), and control \(D_s\), moving endpoints, and the reselected real speeds. The identity (OS9) is a **paper-level reduction**, not a proof of these inputs or a new Lean acceptance.


## Correction: retain the original anchor on the backward overlap (2026-11-11)

The earlier statement that one must first re-anchor the overlap and reassemble the compatibility matrix is superseded. The actual matched Kummer solution is classical at every positive point below the basis radius. Restriction to [L/2,L] retains the original anchor L, the actual zero mismatch jet and the original unique speed. See the complete fixed-domain proof in `HBL_213_FIXED_DOMAIN_SOURCE_STABILITY_20261111.tex` and strict audit record `HBL_213_FIXED_DOMAIN_PARAMETER_STRICT_20261111.md`.

This does not discard nonlocal feedback: replacing the old inner field u by v+chi(u-v) changes the profile by P=(chi-1)(u-v), which must enter the actual source and selection equation. Fixed-domain source differentiation avoids a third interface jet and curvature trace. Producing the actual source time/difference estimates in the original weighted topology remains open; original count 11/13.
