# HBL §2.13 — exact outer-moving Hartree mixed expansion and logarithmic channel

12 November 2026 UTC. **Paper-level derivation only; not a strict Lean acceptance. Revised original theorem count 11/13.** This extends the preceding **fixed-core** mixed calculation to the genuinely moving spatial scale \(r\asymp\ell^{-1}\). It does not assume a Type-II rate, a selected speed, a spectral gap, or any independent positive-time remainder bound.

## 1. True quartic source and exact moving coordinates

Put \(K(x)=|x|^{-2}\), \(W(x)=(1+|x|^2)^{-1/2}\), and let \(z=z(t,v)\) be radial and Schwartz. At a fixed time \(t\), it may be a smooth solution of the original energy-critical three-dimensional Hartree equation
\[
 iz_t+\Delta z+\kappa_H(K*|z|^4)|z|^2z=0.
 \tag{OM1}
\]
Write
\[
 Z_{\ell,t}(x)=\sqrt\ell\,z(t,\ell x),\qquad
 Q_{\ell,t}=K*(|W+Z_{\ell,t}|^4-W^4).
\]
For \(y=\ell x\neq0\), define the **exact rescaled core tail**
\[
 g_\ell(v)=\frac{\sqrt\ell}{\sqrt{\ell^2+|v|^2}}.
\]
Since \(W(v/\ell)=\sqrt\ell\,g_\ell(v)\), the original kernel homogeneity gives, **without any cutoff**,
\[
 \boxed{
 Q_{\ell,t}(y/\ell)=\ell K*\bigl[
 |z+g_\ell|^4-g_\ell^4\bigr](y).}
 \tag{OM2}
\]
For the actual complex radiation and real \(g_\ell\), expansion of the original quartic source is exactly
\[
 \begin{split}
 |z+g_\ell|^4-g_\ell^4={}&|z|^4
 +4g_\ell\,\operatorname{Re}z\,|z|^2\\
 &+g_\ell^2\bigl(2|z|^2+4(\operatorname{Re}z)^2\bigr)
 +4g_\ell^3\,\operatorname{Re}z.
 \end{split}
 \tag{OM3}
\]
No local-NLS substitution and no loss of the global pure radiation contribution occurs.

Define the three literal full-space potentials
\[
 \begin{split}
 H_t(y)&=K*|z(t)|^4(y),\\
 C_t(y)&=K*\bigl[|v|^{-1}\operatorname{Re}z(t,v)|z(t,v)|^2\bigr](y),\\
 D_t(y)&=K*\bigl[|v|^{-2}\{2|z(t,v)|^2
       +4(\operatorname{Re}z(t,v))^2\}\bigr](y).
 \end{split}
 \tag{OM4}
\]
These convolutions exist and are locally smooth for \(y\neq0\) under the stated Schwartz/radial conditions.

## 2. Outer annular asymptotic, including the borderline log

For every compact \(\mathcal A\Subset\mathbb R^3\setminus\{0\}\), uniformly in \(y\in\mathcal A\),
\[
 \boxed{\begin{aligned}
 Q_{\ell,t}(y/\ell)={}&
 \ell H_t(y)+4\ell^{3/2}C_t(y)+\ell^2D_t(y)\\
 &+16\pi\,\ell^{5/2}\log(1/\ell)\,
      \frac{\operatorname{Re}z(t,0)}{|y|^2}
 +O_{t,\mathcal A}(\ell^{5/2}).
 \end{aligned}}
 \tag{OM5}
\]
Thus the first mixed correction **on the moving far annulus** is of order \(\ell^{3/2}\), rather than the \(\ell^{1/2}\) first mixed correction on fixed spatial cores. The \(\ell^{5/2}\log(1/\ell)\) channel is a genuine borderline signature of the cubic-in-core quartic-density monomial; it is not captured by the fixed-core expansion.

Proof. In (OM3), use
\[
 g_\ell(v)=\sqrt\ell(\ell^2+|v|^2)^{-1/2}.
\]
For \(y\in\mathcal A\), splitting \(|v|\le\ell\), \(\ell<|v|<1\), and \(|v|\ge1\), and separately controlling the integrable Riesz singularity at \(v=y\), gives
\[
 \begin{aligned}
 &\ell K*\!\left[g_\ell \operatorname{Re}z\,|z|^2\right](y)
   =\ell^{3/2}C_t(y)
     +O_{\mathcal A}(\ell^{7/2}(1+|\log\ell|)),\\
 &\ell K*\!\left[g_\ell^2
       (2|z|^2+4(\operatorname{Re}z)^2)\right](y)
   =\ell^2D_t(y)+O_{\mathcal A}(\ell^3).
 \end{aligned}
 \tag{OM6}
\]
For the last monomial, the only logarithmic divergence in the rescaled integral is at \(v=0\), where the kernel \(K(y-v)\operatorname{Re}z(v)\) has value
\(|y|^{-2}\operatorname{Re}z(0)\). Indeed, for fixed \(0<\delta<\operatorname{dist}(\mathcal A,0)/2\),
\[
 \begin{aligned}
 &\int_{|v|<\delta}
    \frac{dv}{(\ell^2+|v|^2)^{3/2}}\\
 &\qquad=4\pi\left[
  \operatorname{arsinh}(\delta/\ell)
     -\frac{\delta}{\sqrt{\ell^2+\delta^2}}\right]
   =4\pi\log(1/\ell)+O_\delta(1).
 \end{aligned}
 \tag{OM7}
\]
Subtracting the constant
\(|y|^{-2}\operatorname{Re}z(0)\) in the near-zero integral
makes the remainder absolutely integrable uniformly on \(\mathcal A\).
On \(|v|\ge\delta\) the integrand is uniformly integrable,
including its near-diagonal \(K(y-v)\) singularity. Consequently,
\[
 \ell K*[g_\ell^3\operatorname{Re}z](y)
  =4\pi\,\ell^{5/2}\log(1/\ell)
    \frac{\operatorname{Re}z(0)}{|y|^2}
    +O_{\mathcal A}(\ell^{5/2}).
 \tag{OM8}
\]
Multiplication by 4 proves (OM5). It also explains why no unproved small global \(L^3\) potential bound has been used.

### Coefficient check against the exact fixed-core Green profile

The preceding exact fixed-core convolution
\[
 A(r)=K*W^3(r)
 =\frac{4\pi\operatorname{arsinh}r}{r\sqrt{1+r^2}}
 =\frac{4\pi\log(2r)}{r^2}+O(r^{-4}\log r)
 \qquad(r\to\infty)
\]
has the *formal* large-radius linear channel \(4\sqrt\ell\,c(t)A(r)\).
At \(r=|y|/\ell\), this expression has leading logarithmic
coefficient
\[
 4\sqrt\ell\,c(t)A(|y|/\ell)
 =16\pi c(t)\ell^{5/2}|y|^{-2}\log(1/\ell)
  +O_y(\ell^{5/2}).
 \tag{OM8a}
\]
This **exactly agrees** with the independently obtained moving-annulus
coefficient in (OM5), supplying a useful check that the same core--radiation
cross monomial is retained in both coordinate systems. The older
fixed-core asymptotic is not uniform at \(r=|y|/\ell\), so (OM8a) is a
coefficient consistency check rather than a justification for substituting
moving radii into that expansion.

## 3. Original critical-clock covariant time derivative

Let \(\ell_s=-b\ell\), \(t_s=\ell^2\) and \(D_b=\partial_s+b(1+x\cdot\nabla_x)\). For a term \(\ell^\alpha F_t(\ell x)\), the exact chain rule is
\[
 \boxed{
 D_b[\ell^\alpha F_t(\ell x)]
   =(1-\alpha)b\,\ell^\alpha F_t(\ell x)
    +\ell^{\alpha+2}\partial_tF_t(\ell x).}
 \tag{OM9}
\]
No relation between \(\ell\) and the renormalized time \(s\) is assumed. If \(z,z_t\) have locally uniform Schwartz bounds, differentiating the integral remainder of (OM5) in \(\ell\) is justified on the moving compact annulus. Thus, for \(y=\ell(s)x\in\mathcal A\),
\[
 \boxed{
 D_bQ(s,y/\ell)=
 -2b\ell^{3/2}C_t(y)-b\ell^2D_t(y)
 +\ell^3\partial_tH_t(y)
 +O_{t,\mathcal A}\!\left(
 |b|\ell^{5/2}(1+|\log\ell|)
 +\ell^{7/2}\right).
 }
 \tag{OM10}
\]
In particular, the order-\(\ell\) pure-radiation potential is *exactly* killed by the transport covariance (up to its genuine \(\ell^3H_t\) physical PDE derivative), but the outer mixed \(\ell^{3/2}C_t\) contribution survives as \(-2b\ell^{3/2}C_t\).

For a nonnegative, nonzero radial real Schwartz snapshot (e.g. \(z(t_0,v)=e^{-|v|^2}\)), \(C_t(y)>0\) for all \(y\neq0\). At that snapshot the genuine Hartree PDE makes \(z_t\) purely imaginary and \(H_t'=0\) as a time derivative. Hence the mixed covariant channel is not an artifact of freely prescribing a fake radiation source. Nevertheless, this **does not** determine the unique selected HBL speed \(b\), and it is not a lower bound for the original four-piece forcing norm.

## 4. Precise original-paper gate and audit boundary

(OM5) and (OM10) supply a missing complementary expansion to the preceding *fixed-core* \(\sqrt\ell\)-profile. They are conditional on genuinely smooth Schwartz **test** radiation snapshots; they are not promoted to estimates on the unknown selected HBL profile. They show that the full mixed Hartree interaction must be transported through the actual unique two-real-speed Cramer selector and the moving Kummer correction on the annular region \(r\sim\ell^{-1}\). A constant phase/frequency mode does not automatically remove the nonconstant \(C_t(y)\) channel.

Still required: derive actual physical-orbit parameter/time regularity and selected-speed differentiation; prove full nonlocal **four-region** weighted PDE residual positive \(s\)-order and parameter Lipschitz, with all moving endpoints, then genuine finite iteration and dynamically selected Type-II rate. Nothing in (OM5)/(OM10) alone gives such a gain.

Original Lean audited prior **successes**, not new audits: [43135036481](https://github.com/penghongzhong/HBL/actions/runs/43135036481), job 130908225390 (selected spectral quadratic / 3 \(C^1\)); [43124289518](https://github.com/penghongzhong/HBL/actions/runs/43124289518), job 130872307063 (four-piece nonlinear PDE telescoping). Original theorem count remains **11/13**. This paper computation has **no** Lean CI or authorized axiom conclusion.
