# HBL §2.13 — Localized remote Hartree potential from the physical inverse-square moment

11 November 2026. Paper-level analytic lemma only. **Strict original environment count stays 11/13.** This corrects the *scope* of the preceding volume-moment note: although the exterior multipole coefficient is a volume moment, **a separate volume-moment bound is not required to estimate the localized inner contribution at the original backward overlap**. No global-time gain or original theorem is claimed.

## Genuine radial inverse-square kernel

Fix L>0, R=L/3 and a real density rho with J=4 pi ∫_0^R |rho(q)| dq<∞. Extend rho by zero for q>R. The actual 3D potential, for r>R, is

\[
 Q_\rho(r)=\frac{2\pi}{r}\int_0^R q\rho(q)\log\frac{r+q}{r-q}\,dq
 =4\pi\sum_{j=0}^\infty
 \frac{\int_0^R q^{2j+2}\rho(q)\,dq}{(2j+1)r^{2j+2}}.
 \tag{IM1}
\]

All derivatives below are legitimate by absolutely locally uniform convergence for r>R. The estimates
\[
 \left|\int_0^R q^{2j+2}\rho(q)dq\right|\le R^{2j+2}\frac{J}{4\pi},
 \quad \frac{2j+2}{2j+1}\le2,\quad
 \frac{(2j+2)(2j+3)}{2j+1}\le6(j+1)
\]
give
\[
 |Q_\rho(r)|\le\frac{R^2J}{r^2-R^2},\quad
 |Q'_\rho(r)|\le\frac{2R^2J}{r(r^2-R^2)},\quad
 |Q''_\rho(r)|\le\frac{6R^2J}{(r^2-R^2)^2}.
 \tag{IM2}
\]
At the *literal* matched backward overlap 3L/4<=r<=L,
\[
 \boxed{|Q_\rho|\le\frac{16}{65}J,\quad
 |Q'_\rho|\le\frac{128}{195L}J,\quad
 |Q''_\rho|\le\frac{13824}{4225L^2}J.}
 \tag{IM3}
\]
The rational coefficients were independently checked using R=L/3 and r=3L/4. The radius powers offset the earlier ratio between the volume quartic moment and inverse-square quartic moment. The untruncated outer/near-diagonal density remains outside the scope of IM3.

## Actual quartic density difference and critical rescaling

For complex radial fields u,v write rho=|u|^4-|v|^4 and M(w)=4 pi∫_0^∞|w(q)|^4dq, exactly the radial form of the repository's actualPhysicalInverseSquareMoment. Holder, Minkowski and
\[
 \bigl||u|^4-|v|^4\bigr|\le4(|u|+|v|)^3|u-v|
\]
give the **difference**, not merely single-field, estimate
\[
 J\le4\bigl(M(u)^{1/4}+M(v)^{1/4}\bigr)^3 M(u-v)^{1/4}.
 \tag{IM4}
\]
For the *exact previously verified* critical radiation scaling
Z_ell(q)=sqrt(ell) z(ell q), ell>0, one has M(Z_ell)=ell M(z). For the specifically stated bubble/radiation comparison u=V+Z_ell, v=V, IM3--IM4 imply
\[
 \boxed{\sup_{3L/4\le r\le L}
 |Q_{(|V+Z_\ell|^4-|V|^4)\mathbf1_{[0,L/3]}}(r)|
 \le\frac{64}{65}
 [2M(V)^{1/4}+(\ell M(z))^{1/4}]^3
 (\ell M(z))^{1/4}.}
 \tag{IM5}
\]
For bounded physical z-moment this is O(ell^(1/4)) as ell tends to zero, **not** an established positive temporal order. Nor is the full spectral four-piece difference equal to Z_ell.

## Moving interfaces: actual cutoff derivative and first C1 trace

Choose C1 chi with chi=1 on [0,1/4], chi=0 on [1/3,infinity), 0<=chi<=1 and C_chi=sup|chi'|. Set Q_L(s,r)=K*(chi(q/L(s))rho(s,q))(r). Under legitimate differentiation and finite
J0=4pi∫_0^(L/3)|rho|dq, J1=4pi∫_0^(L/3)|partial_s rho|dq, one has exactly
\[
 \partial_s(\chi(q/L)\rho)
 =\chi(q/L)\partial_s\rho-\frac{L'}L\frac qL\chi'(q/L)\rho .
 \tag{IM6}
\]
Thus at fixed r in the overlap,
\[
 |\partial_s Q_L|\le\frac{16}{65}
 (J_1+\frac{C_\chi|L'|}{3L}J_0),\quad
 |\partial_s\partial_r Q_L|\le\frac{128}{195L}
 (J_1+\frac{C_\chi|L'|}{3L}J_0).
 \tag{IM7}
\]
At moving r=theta L(s), theta fixed in [3/4,1], the *complete chain rule*, including evaluation-point motion, gives
\[
 \boxed{\left|\frac d{ds}Q_L(s,\theta L(s))\right|
 \le\frac{16}{65}J_1+
 \frac{16C_\chi+128\theta}{195}\frac{|L'|}{L}J_0,}
 \tag{IM8}
\]
\[
 \boxed{\left|\frac d{ds}\partial_r Q_L(s,\theta L(s))\right|
 \le\frac{128}{195L}J_1+
 \left(\frac{128C_\chi}{585}
 +\frac{13824\theta}{4225}\right)\frac{|L'|}{L^2}J_0.}
 \tag{IM9}
\]
No hard-cutoff density trace, prescribed rate or hidden left Kummer radius r0=L/a is used. These formulas are conditional on actual J1 and L' and do not produce their decay.

## Precise verification boundary

The original telescope initially failed in CI 42530158681 due to upstream InWeightedL2 and type issues. CI 42958494409, original job 130319187052, is Success under pinned Lean 4.35.0-rc3 / Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, --trust=0 and warningAsError. Exact #check and #print axioms for its four specified declarations show only propext, Classical.choice and Quot.sound. **This is an algebraic PDE telescope; no strict CI audits IM1--IM9.**

What is still open: actual same-PDE-orbit bounds on J0 and J1 for the **selected complete four-piece difference**, the untruncated near-diagonal outer density, moving Kummer basis/endpoint/unique two-speed derivatives, complete strong residual positive time order and parameter Lipschitz, true finite recursion and a PDE-derived Type-II rate. No independent source envelope or rate has been inserted. Revised originals **11/13**.


## 5. Actual PDE generation of the density-velocity budget for the physical radiation channel

The term J1 in (IM7)--(IM9) need not be **postulated** for the special physical bubble-plus-radiation channel. Let the physical radiation z(t,q) solve the ORIGINAL (nonlocal) equation
\[
 iz_t+\Delta z+{\cal N}_H(z)=0,\quad
 {\cal N}_H(z)=\kappa_H(|x|^{-2}*|z|^4)|z|^2z.
\]
Let ell(s)>0, ell_s=-b(s)ell(s), t_s=ell(s)^2, and Z(s,r)=sqrt(ell(s))*z(t(s),ell(s)r), evaluated at fixed r. The complete chain rule yields
\[
 \boxed{Z_s=-b\left(\frac12 Z+rZ_r\right)
   +i\ell^{5/2}[\Delta z+{\cal N}_H(z)](t,\ell r).}
 \tag{IM10}
\]
There is no freely assigned temporal source bound in this identity. Put
\[
 A={\cal M}(V)^{1/4},\quad
 B={\cal M}(z(t))^{1/4},\quad
 D={\cal M}(qz_q(t,q))^{1/4},\quad
 P={\cal M}((\Delta z+{\cal N}_H(z))(t))^{1/4}
\]
and assume these quantities are finite, with fixed background V independent of s.
The exact L4(dr) scaling gives
\[
 \boxed{{\cal M}(Z_s)^{1/4}
 \le\ell^{1/4}|b|(B/2+D)+\ell^{9/4}P.}
 \tag{IM11}
\]
For rho(s,r)=|V(r)+Z(s,r)|^4-|V(r)|^4, the genuine density and its time derivative therefore satisfy
\[
 \boxed{J_0\le4(2A+\ell^{1/4}B)^3\ell^{1/4}B,\quad
 J_1\le4(A+\ell^{1/4}B)^3
  [\ell^{1/4}|b|(B/2+D)+\ell^{9/4}P].}
 \tag{IM12}
\]
Inserting (IM12) into (IM8)--(IM9) is a completely explicit source-derived moving-potential bound in the original physical scaling, with no new volume moment or independent density-velocity rate. It **does not** bound P, D, b, L'/L or their full assembled-packet analogues; those are true regular-flow and modulation obligations, and no decay in s follows without them. If z solves a forced equation, IM10 must retain its actual forcing as an additional term.

A second useful parameter interface follows by differentiating the *same* physical scaling at fixed t:
\[
 \partial_{\log\ell} Z_\ell=\frac12 Z_\ell+r\partial_r Z_\ell,\qquad
 \|\partial_{\log\ell}Z_\ell\|_{L^4(4\pi dr)}
 \le\ell^{1/4}(B/2+D).
 \tag{IM13}
\]
Integrating in log ell for 0<ell1,ell2 with fixed physical z gives the non-singular parameter estimate
\[
 \boxed{\|Z_{\ell_1}-Z_{\ell_2}\|_{L^4(4\pi dr)}
 \le4(B/2+D)|\ell_1^{1/4}-\ell_2^{1/4}|.}
 \tag{IM14}
\]
Time variation of z and spectral/Kummer parameters cannot be discarded when using IM14 for the actual moving four-piece packet. Equations IM10--IM14 are newly derived paper-level consequences of the physical PDE and radial rescaling, not yet Lean compiled. **Original count remains 11/13.**
