# HBL §2.13 — source-faithful singular Green Cramer feedback from a shell-supported true Hartree correction

**11 November 2026. Paper proof, not a new Lean declaration. Revised original acceptance: 11/13.**

## 1. Statement in the ORIGINAL Kummer basis

Let \(0<r_0<B\), \(a>0\), and take the actual origin-normalized Kummer pair in
`HBL/KummerOriginGreen/GreenBridge.lean`:
\[
Y_K(r)=K.y(r)/r,\qquad W_K(r)=r^{-2}e^{-ir^2/4},\qquad
C_Y=\sup_{0\le r\le B}|K.y(r)|<\infty .
\]
The **singular** original coefficient of a radial source \(F\) is
\[
\mathcal C_B^K[F]=\int_{r_0}^{B}Y_K(r)e^{ir^2/4}r^2F(r)\,dr.
\tag{SB1}
\]
Put \(\mathcal N_H(U)=\kappa_H(|x|^{-2}*|U|^4)|U|^2U\), with
\(\kappa_H>0\). Let \(U,P\in\dot H^1_{\rm rad}(\mathbb R^3;\mathbb C)\),
and assume that the **physical correction itself**, not the convolution,
is supported in the actual annulus
\[
\operatorname{supp}P\subseteq \{L\le |x|\le L+h\},
\qquad L,h>0.
\]
Define \(\delta\rho=|U+P|^4-|U|^4\),
\(\delta\mathcal N=\mathcal N_H(U+P)-\mathcal N_H(U)\),
\(F_a(r)=a^2\delta\mathcal N(ar)\), and
\[
E=\|\nabla U\|_2,\quad
A=2\|U\|_6+\|P\|_6,\quad D=\|P\|_6,\quad
V_{L,h}=\frac{4\pi}{3}((L+h)^3-L^3).
\]
Then the **entire, genuine quartic nonlocal feedback** obeys
\[
\boxed{\begin{aligned}
|\mathcal C_B^K[F_a]|
\le C_Y\kappa_H\Big[
&\frac{16\sqrt2}{(4\pi)^{3/2}}
 E^3L^{-3/2}V_{L,h}^{1/3}A^3D\\
&+\frac{7C_{\rm HLS}}{4\pi}
 \left(\frac{32\pi}{3}\right)^{1/6}
 L^{-1/2}A^6D\Big].
\end{aligned}}\tag{SB2}
\]
**No negative power of the Green left endpoint \(r_0\)** occurs. The
physical shell radius \(L\) is a genuine geometric parameter and is
not silently identified with \(r_0\); the Kummer scaling \(a\)
cancels exactly in the singular integral. The bound is at a fixed
Kummer basis; uniformity of \(C_Y\) along moving physical parameters
has NOT been proved here.

## 2. Derivation with the true nonlocal convolution

For radial energy-class \(U\), the fundamental theorem of calculus
and Cauchy–Schwarz in the physical \(4\pi r^2dr\) measure give the
radial Strauss estimate (first for smooth compact radial functions;
then for the radial \(\dot H^1\) representative):
\[
|U(r)|\le (4\pi)^{-1/2}r^{-1/2}\|\nabla U\|_2.
\tag{SB3}
\]
The density difference is supported in the **same** annulus as \(P\).
Hölder on that finite-volume annulus and the elementary fourth-power
difference give
\[
\|\delta\rho\|_1
\le4V_{L,h}^{1/3}A^3D.
\tag{SB4}
\]
For \(|x|\le L/2\) and \(|y|\ge L\), \(|x-y|\ge L/2\). Hence the
**actual** convolution perturbation satisfies
\[
|(|x|^{-2}*\delta\rho)(x)|
\le4L^{-2}\|\delta\rho\|_1.
\tag{SB5}
\]
Although \(\delta\mathcal N\) is generally NONZERO in this inner
region, \(P(x)=0\) there and therefore
\[
\delta\mathcal N(x)
=\kappa_H(|x|^{-2}*\delta\rho)(x)|U(x)|^2U(x).
\]
By (SB3)–(SB5),
\[
\begin{aligned}
\int_0^{L/2}r|\delta\mathcal N(r)|\,dr
&\le4\kappa_HL^{-2}\|\delta\rho\|_1
  (4\pi)^{-3/2}E^3\int_0^{L/2}r^{-1/2}dr\\
&=\frac{4\sqrt2\kappa_H}{(4\pi)^{3/2}}
  E^3L^{-3/2}\|\delta\rho\|_1\\
&\le\frac{16\sqrt2\kappa_H}{(4\pi)^{3/2}}
  E^3L^{-3/2}V_{L,h}^{1/3}A^3D.
\end{aligned}\tag{SB6}
\]
For the complementary interval use the same HLS/Hölder estimate
as (NF1)/(AC4) in the companion paper:
\[
\|\delta\mathcal N\|_{6/5}
\le7\kappa_H C_{\rm HLS}A^6D.
\]
The physical radial measure, rather than one-dimensional Lebesgue
measure, gives exactly
\[
\begin{aligned}
\int_{L/2}^{\infty}r|\delta\mathcal N(r)|\,dr
&=\frac1{4\pi}\int_{|x|\ge L/2}|x|^{-1}|\delta\mathcal N(x)|\,dx\\
&\le\frac1{4\pi}
\left(4\pi\int_{L/2}^{\infty}r^{-4}dr\right)^{1/6}
\|\delta\mathcal N\|_{6/5}\\
&\le\frac{7\kappa_HC_{\rm HLS}}{4\pi}
\left(\frac{32\pi}{3}\right)^{1/6}
 L^{-1/2}A^6D.
\end{aligned}\tag{SB7}
\]
Finally, the **exact original** Wronskian in (SB1), with
\(y=ar\), shows
\[
\mathcal C_B^K[F_a]
=\int_{ar_0}^{aB}K.y(y/a)e^{iy^2/(4a^2)}
\,y\,\delta\mathcal N(y)\,dy.
\tag{SB8}
\]
The two bounds (SB6)–(SB7), together with \(|K.y|\le C_Y\),
give (SB2) with no \(r_0^{-1/2}\) loss.

## 2a. Explicit geometric gain on the actual large-radius overlap

If \(0<h\le L\), then
\[
V_{L,h}\le\frac{28\pi}{3}L^3,\qquad
L^{-3/2}V_{L,h}^{1/3}\le
\left(\frac{28\pi}{3}\right)^{1/3}L^{-1/2}.
\]
Consequently (SB2) implies the single-factor estimate
\[
|\mathcal C_B^K[F_a]|
\le C_Y\kappa_H L^{-1/2}D
\left[
\frac{16\sqrt2}{(4\pi)^{3/2}}
\left(\frac{28\pi}{3}\right)^{1/3}E^3A^3
+\frac{7C_{\rm HLS}}{4\pi}
\left(\frac{32\pi}{3}\right)^{1/6}A^6
\right].
\tag{SB10}
\]
In the current slow-inner overlap convention \(L=\ell^{-1/16}\),
this produces a **geometric** \(\ell^{1/32}\) factor *provided*
\(C_Y,E,A,D\) remain suitably controlled along the actual packet.
It is NOT a time-positive original PDE residual bound, and no blowup
rate or time law for \(\ell\) is inferred.

## 3. Exact relation to the current C³ repair and the acceptance gate

For the original source-generated Hermite correction
\[
P(r)=h^2d_2\phi_2((r-L)/h)
 +h^3d_3\phi_3((r-L)/h)
\quad (L\le r\le L+h),
\]
the already checked *paper* shell integral gives
\[
D\le V_{L,h}^{1/6}
\big(h^2|d_2|M_2+h^3|d_3|M_3\big).
\tag{SB9}
\]
Substitution of (SB9) into (SB2) expresses the singular-channel
nonlinear feedback **in actual repair jets** rather than an independent
source envelope. This is a mathematically different bound from the
sharp \(r_0^{-1/2}\) obstruction for *arbitrary* \(L^{6/5}\)
forcing: it exploits both exact nonlocal Hartree algebra and the
positive-radius support of the real physical correction, while also
controlling the nonlocal change INSIDE the shell.

**Not discharged:** proof that the actual one-orbit correction enjoys
the needed fixed physical shell support and bounds for \(d_2,d_3\)
(and their time/parameter variations) in the retained packet; the
moving-basis uniform \(C_Y\); the Cramer selector's complete
two-real-speed Jacobian; the unperturbed/background original PDE
residual; positive time order and parameter Lipschitz; and physical
finite recursion/dynamical II-type rate. This is a new *paper-level*
nonlocal-feedback lemma, not a new Lean theorem or acceptance of §2.13.
Original revised count remains **11/13**.
