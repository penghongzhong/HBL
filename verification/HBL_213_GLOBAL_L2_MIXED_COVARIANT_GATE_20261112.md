# HBL §2.13: global L2 gate for the original mixed Hartree covariant flux

12 November 2026 UTC. **Paper proof only: not Lean accepted. Revised original environments 11/13.**

## Theorem (complete original quartic source, global critical norm)

Let K(x)=|x|^{-2}, W(x)=(1+|x|^2)^{-1/2} in R^3. Let z(t,x) be a smooth radial Schwartz trajectory of the **actual** critical Hartree PDE
\[
iz_t+\Delta z+\kappa_H(K*|z|^4)|z|^2z=0
\]
with uniform Schwartz bounds for z and z_t on a fixed physical-time interval. The smoothness is a test-trajectory assumption, NOT a bound derived for the unknown selected HBL orbit. Define
\[
Z(s,x)=\sqrt{\ell(s)}z(t(s),\ell(s)x),\quad
Q=K*(|W+Z|^4-W^4),\quad
\ell_s=-b\ell,\quad t_s=\ell^2,\quad0<\ell\le1,
\]
\[
D_b=\partial_s+b(1+x\cdot\nabla_x),\qquad
C_t=K*\left[|v|^{-1}\operatorname{Re}z(t,v)|z(t,v)|^2\right],\qquad
(T_\ell f)(x)=\ell^{3/2}f(\ell x).
\]
There is M depending only on the Schwartz seminorm bounds and the fixed HLS constant such that
\[
\boxed{\ \|T_\ell^{-1}D_bQ+2bC_t\|_{L^2(\mathbb R^3)}
 \le M(|b|\ell^{1/2}+\ell^{3/2}).\ }\tag{GL1}
\]
Equivalently, the same right side bounds
\[
\|D_bQ+2b\ell^{3/2}C_t(\ell\cdot)\|_{L^2_x}.\tag{GL2}
\]
This includes all genuine mixed nonlocal terms. The operator T_ell is an L2 isometry; HLS maps K*:L^{6/5}->L2, so C_t belongs to L2.

## Proof

Set y=ell*x, r=|v|, g_ell(v)=sqrt(ell)/sqrt(ell^2+r^2),
w=Re z, h=|z|^2, m=2h+4w^2, and
rho_ell,t=|z+g_ell|^4-g_ell^4. Exact kernel homogeneity yields
\[
Q(s,x)=\ell(K*\rho_{\ell,t})(\ell x),\qquad
\rho_{\ell,t}=h^2+4g_\ell wh+g_\ell^2m+4g_\ell^3w.\tag{GL3}
\]
Using the real critical clock, all bare transport terms cancel *before* applying absolute-value estimates:
\[
D_bQ=-b\ell^2(K*\partial_\ell\rho_{\ell,t})(\ell x)
        +\ell^3(K*\partial_t\rho_{\ell,t})(\ell x),
\]
\[
T_\ell^{-1}D_bQ=-bK*[\ell^{1/2}\partial_\ell\rho_{\ell,t}]
                 +\ell^{3/2}K*[\partial_t\rho_{\ell,t}].\tag{GL4}
\]
All differentiations are justified in L^{6/5} under the stated Schwartz regularity.

The exact core-tail derivatives are
\[
\begin{aligned}
\ell^{1/2}\partial_\ell g_\ell
 &=\tfrac12(\ell^2+r^2)^{-1/2}-\ell^2(\ell^2+r^2)^{-3/2},\\
\ell^{1/2}\partial_\ell(g_\ell^2)
 &=\ell^{1/2}[(\ell^2+r^2)^{-1}-2\ell^2(\ell^2+r^2)^{-2}],\\
\ell^{1/2}\partial_\ell(g_\ell^3)
 &=\tfrac32\ell(\ell^2+r^2)^{-3/2}
     -3\ell^3(\ell^2+r^2)^{-5/2}.
\end{aligned}\tag{GL5}
\]
Take p=6/5, so 3/p=5/2. Rescaling v=ell*u and using the cancellation of the leading far-field inverse-radius tail proves
\[
\|(\ell^2+r^2)^{-1/2}-r^{-1}\|_p
+\|\ell^2(\ell^2+r^2)^{-3/2}\|_p\le C\ell^{3/2}.\tag{GL6}
\]
(The first difference decays as r^{-3} at infinity and is r^{-1} at zero; both are L^p integrable.) Since 2p=12/5<3,
\[
\|\ell^{1/2}\partial_\ell(g_\ell^2)m\|_p
 \le 3\ell^{1/2}\|r^{-2}m\|_p,\tag{GL7}
\]
and scaling the last two kernels in (GL5) yields
\[
\|\ell^{1/2}\partial_\ell(g_\ell^3)w\|_p
 \le C\ell^{1/2}\|w\|_\infty.\tag{GL8}
\]
The physical-time derivative obeys
\(\sup_{0<\ell\le1}\|\partial_t\rho_{\ell,t}\|_p<\infty\);
indeed z,z_t and their products are Schwartz and each g_ell power
is integrable against the corresponding physical-time derivative.
Together,
\[
\|\ell^{1/2}\partial_\ell\rho_{\ell,t}
 -2r^{-1}wh\|_{6/5}\le C\ell^{1/2}.\tag{GL9}
\]
Apply the **original** Riesz/HLS estimate \(K*:L^{6/5}\to L^2\)
to (GL4),(GL9), proving (GL1).

## Genuine obstruction to a shortcut

At a real positive Gaussian snapshot z(t_*,v)=e^{-|v|^2},
the true Hartree local flow is a suitable smooth test trajectory.
Its C_{t_*}(y)>0 for every y and \(0<\|C_{t_*}\|_2<\infty\).
If ell(s)->0, b(s)->b_* not equal 0, and t(s)->t_*,
then continuity in Schwartz topology and (GL1) imply
\[
\boxed{\lim_s\|D_bQ(s)\|_{L^2_x}
 =2|b_*|\|C_{t_*}\|_{L^2_y}>0.}\tag{GL10}
\]
Thus the moving-annulus *pointwise* mixed contribution
O(|b|ell^{3/2}) has **no global unweighted L2 scale gain**:
the annulus volume is O(ell^{-3}), precisely canceling the pointwise
L2 scaling. The actual HBL selected b may tend to zero and the genuine
Kummer correction may cancel this channel. Therefore (GL10) does NOT
disprove the original main theorem or give a lower bound on its
complete weighted four-region PDE residual.

**Next precise load-bearing target:** establish cancellation of the
critical 2b*C_t channel under the SAME actual two-real-speed Cramer
selector, moving Kummer coefficients/endpoints and true three C1 joins,
or prove a genuine selected-orbit bound in the ORIGINAL weighted residual
space. Then derive positive renormalized-time order, parameter Lipschitz,
finite physical recursion and the dynamical Type-II rate. Do not
postulate a rate, spectral derivative budget or independent envelope.

**Exact previously successful CI logs rechecked:** 42531450638,
42531500587, 42531018076, 42530313725, 42529092477.
Historical 42531033761/768, 42531467165/166, 42530158681 failed
on upstream InWeightedL2/type issues. Superseding strict successes:
https://github.com/penghongzhong/HBL/actions/runs/43135036481
(job 130908225390, frozen selected quadratic + three C1)
and https://github.com/penghongzhong/HBL/actions/runs/43124289518
(job 130872307063, finite nonlinear PDE telescope **identity**).
Their original logs confirm Lean 4.35.0-rc3,
Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5,
--trust=0, warningAsError, exact #check and #print axioms
with only propext/Classical.choice/Quot.sound on the audited types.
**No new Lean CI tests (GL1)-(GL10); no new original environment closure.
Official 11/13 (84.62%).**
