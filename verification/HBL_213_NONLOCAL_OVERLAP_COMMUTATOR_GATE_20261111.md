# HBL §2.13: exact nonlocal overlap commutator and a global-source obstruction

11 November 2026. **Paper-only mathematical audit; original revised environments remain 11/13.** This note concerns the original three-dimensional inverse-square *quartic-density* Hartree nonlinearity, not a local cubic substitute. It identifies exactly which global nonlocal quantity must supplement the previously proved backward Volterra estimates.

## Exact first variation of the genuine seven-linear Hartree source

Put
\[
 K(x)=|x|^{-2},\qquad
 {\cal N}_H(q)=\kappa_H(K*|q|^4)|q|^2q,\qquad
 0\leq\eta(x)\leq1,
\]
with \(\eta\) real, smooth and radial. For smooth radial fields \(u,v\in \dot H^1(\mathbb R^3)\), let
\[
 f=u-v,\quad U=(1-\eta)u+\eta v=u-\eta f,\quad
 {\cal C}_\eta(u,v)
 ={\cal N}_H(U)-(1-\eta){\cal N}_H(u)-\eta{\cal N}_H(v).
 \tag{NC1}
\]
All Hartree potentials in (NC1) are computed from the **full three-dimensional fields**, not from their annular restrictions.

The real Fréchet derivative of the original nonlinear map is
\[
 \begin{aligned}
 D{\cal N}_H(u)[h]
 =\kappa_H\bigl(K*(4|u|^2\operatorname{Re}(\bar u h))\bigr)|u|^2u\\
 \quad+\kappa_H(K*|u|^4)
 \bigl(|u|^2h+2u\operatorname{Re}(\bar u h)\bigr).
 \end{aligned}
 \tag{NC2}
\]
Indeed, the identities
\(D(|u|^4)[h]=4|u|^2\operatorname{Re}(\bar uh)\) and
\(D(|u|^2u)[h]=|u|^2h+2u\operatorname{Re}(\bar uh)\)
give (NC2) directly. Define
\(g_{u,f}=4|u|^2\operatorname{Re}(\bar u f)\) and
\(v_\epsilon=u-\epsilon f,\ U_\epsilon=u-\epsilon\eta f\).
Then, as \(\epsilon\to0\) in the space \(L^{6/5}(\mathbb R^3)\),
\[
 \boxed{
 \epsilon^{-1}{\cal C}_\eta(u,v_\epsilon)
 \longrightarrow
 \kappa_H|u|^2u\,
 \{\eta[K*g_{u,f}]-K*(\eta g_{u,f})\}.
 }
 \tag{NC3}
\]
The local part of (NC2) cancels because \(\eta\) is real. The **nonlocal commutator survives at first order**, unless the selected physical density/correction has additional cancellation. Thus the overlap error is not generically quadratic in \(u-v\).

## Quantitative global bound in the critical source space

Let \(C_{\rm HLS}\) denote the HLS constant for
\(\|K*h\|_{L^3}\le C_{\rm HLS}\|h\|_{L^{3/2}}\).
For \(p,q\in L^6\),
\[
 \||p|^4-|q|^4\|_{3/2}
 \le4(\|p\|_6+\|q\|_6)^3\|p-q\|_6,
\quad
 \||p|^2p-|q|^2q\|_2
 \le3(\|p\|_6+\|q\|_6)^2\|p-q\|_6.
\]
Hölder and HLS yield
\[
 \|{\cal N}_H(p)-{\cal N}_H(q)\|_{6/5}
 \le 7|\kappa_H|C_{\rm HLS}
       (\|p\|_6+\|q\|_6)^6\|p-q\|_6 .
 \tag{NC4}
\]
Since \(\|U\|_6\le\|u\|_6+\|v\|_6=:E\),
\(\|U-u\|_6\le D:=\|u-v\|_6\) and \(\|\eta\|_\infty\le1\),
the exact defect (NC1) obeys the safe, completely source-faithful bound
\[
 \boxed{
 \|{\cal C}_\eta(u,v)\|_{6/5}
 \le 455|\kappa_H|C_{\rm HLS}\,E^6D .
 }
 \tag{NC5}
\]
(The non-sharp coefficient is \(7(2^6+1)=455\).)
This controls the *full nonlocal interaction*, but demands a **global** \(L^6\) difference, not merely the local Laplacian mismatch on the overlap. Sobolev converts \(D\) to a global \(\dot H^1\) difference only after such a difference has actually been produced by the same PDE construction.

## Exact no-go for a bound depending only on the local Volterra source

Fix \(L>0\) and the **literal coded transition**
\(\eta_L(r)=\chi(8r/L-4)\), with \(\eta_L=0\) on \(r\le5L/8\) and
\(\eta_L=1\) on \(r\ge3L/4\).
Choose nonnegative smooth compactly supported radial functions \(u,f\),
with \(u>0\) on \(0<r<L\), \(f\not\equiv0\) supported on
\(L/8<r<L/3\), and \(0<f<u/2\) wherever \(f>0\). Set
\(v=u-f\) and \(U=u-\eta_Lf\).
Because \(\eta_Lf=0\) globally,
\[
 U=u,\qquad f(L)=f'(L)=0,\qquad
 g:=\Delta_r f=0\quad\text{on }[5L/8,L].
 \tag{NC6}
\]
At any \(x\) with \(3L/4<|x|<L\), one has
\(\eta_L(x)=1\) and \(u(x)=v(x)>0\), but
\[
 \begin{aligned}
 {\cal C}_{\eta_L}(u,v)(x)
 &= {\cal N}_H(u)(x)-{\cal N}_H(v)(x)\\
 &=\kappa_H u(x)^3\int_{\mathbb R^3}
       \frac{u(y)^4-v(y)^4}{|x-y|^2}\,dy ,
 \end{aligned}
 \tag{NC7}
\]
which is **strictly positive if \(\kappa_H>0\)** (nonzero for any
\(\kappa_H\ne0\)). The integral is finite and nonzero. Consequently,
no uniform inequality of the form
\[
 \|{\cal C}_{\eta_L}(u,v)\|_{L^{6/5}(\{3L/4<|x|<L\})}
 \le C(L)\|\Delta_r(u-v)\|_{L^2([5L/8,L],r^2dr)}
 \tag{NC8}
\]
holds for arbitrary smooth radial profiles.

This is a **sharp logical obstruction** to deducing the genuine Hartree
overlap defect from the backward local Volterra source \(g\) alone:
even zero local Cauchy and curvature mismatch cannot eliminate remote
quartic-density feedback. The example does **not** claim to be a
selected solution of the original Hartree PDE, nor does it rule out
dynamical cancellation for that solution.

## Quantitative near/far split: the shortest correct replacement

The Volterra data do control the **local portion** of the global mismatch.
Under the genuine Cauchy match \(f(L)=f'(L)=0\), (WG7) and Cauchy--Schwarz give, with \(A_L=\{5L/8\le|x|\le L\}\),
\[
 |f'(r)|\le r^{-2}
 \Bigl(\int_r^L t^2|g(t)|^2dt\Bigr)^{1/2}
 \Bigl(\int_r^L t^2dt\Bigr)^{1/2}
 \le \frac{64}{25\sqrt3}L^{-1/2}\|g\|_{r,2}.
\]
Consequently
\[
 \|f\|_{L^\infty(A_L)}
 \le \frac{24}{25\sqrt3}L^{1/2}\|g\|_{r,2}.
\]
Since \(|A_L|=(129\pi/128)L^3\), the **three-dimensional critical norm** satisfies
\[
 \boxed{
 \|f\|_{L^6(A_L)}
 \le C_{\rm ann} L\|g\|_{r,2},
 \qquad C_{\rm ann}=\frac{24}{25\sqrt3}
       \Bigl(\frac{129\pi}{128}\Bigr)^{1/6}.
 }\tag{NC9}
\]
Define the indispensable remote mismatch
\[
 D_{\rm rem}=\|f\|_{L^6(\mathbb R^3\setminus A_L)}.
\]
Then \(\|f\|_6\le C_{\rm ann}L\|g\|_{r,2}+D_{\rm rem}\). Inserting this **actual near/far decomposition** into (NC5) gives
\[
 \boxed{
 \|{\cal C}_{\eta_L}(u,v)\|_{6/5}
 \le455|\kappa_H|C_{\rm HLS}E^6
       \left(C_{\rm ann}L\|g\|_{r,2}+D_{\rm rem}\right).
 }\tag{NC10}
\]
This explicitly separates the *already tractable* backward-overlap
curvature mismatch from the **independent global remote-density**
obligation. The no-go example (NC6)--(NC8) has \(g=0\) but
\(D_{\rm rem}>0\), proving the additional term cannot be dropped
without an actual selected-PDE mechanism. No temporal decay of
\(D_{\rm rem}(s)\) has been proved.

## Corrected main-chain interface

The genuine overlapping PDE identity and the spatial/transport
Volterra bounds remain valid, but the nonlinear term requires one
additional global producer: either the complete same-orbit
\(D(s)=\|u(s)-v(s)\|_{L^6(\mathbb R^3)}\) with the required
time-weighted and parameter-Lipschitz estimates, or a direct
estimate of the **actual density commutator** in (NC3) from the
selected Hartree PDE. A small annular \(\|\Delta_r(u-v)\|_2\)
is not a replacement.

The existing strict CI 42958494409 audits only the algebraic finite
PDE telescope under pinned Lean 4.35.0-rc3/Mathlib; neither (NC3) nor
(NC5) nor this no-go example has a strict Lean CI. No claim of a
positive-time four-region residual, finite recursion, dynamically
generated II-type rate or acceptance of original §2.13 is made.
**Revised original-environment count: 11/13 (84.62%).**
