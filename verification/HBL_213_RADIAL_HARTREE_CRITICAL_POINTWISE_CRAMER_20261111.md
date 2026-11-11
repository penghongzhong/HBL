# HBL §2.13: radial-energy critical pointwise estimate for the actual quartic Hartree feedback

**11 November 2026. New complete paper argument, NOT Lean-certified. Formal retained-original acceptance remains 11/13.**

## A. Genuine radial nonlinear estimate (no shell support hypothesis)

Let (u,v\in\dot H^1_{\rm rad}(\mathbb R^3;\mathbb C)), let
\[
\mathcal N_H(w)(x)=\kappa_H\,(|x|^{-2}*|w|^4)(x)|w(x)|^2w(x),
\qquad \kappa_H>0,
\]
and let (S>0) be any constant such that (\|w\|_6\le S\|\nabla w\|_2).
Put (E=\|\nabla u\|_2+\|\nabla v\|_2), (D=\|\nabla(u-v)\|_2), and
\[
c_*=\frac1{\sqrt{4\pi}},\quad
C_*=\frac1{2\pi}+\left(\frac{32\pi}{3}\right)^{1/3}S^4,\quad
C_{\rm pt}=7\kappa_H c_*^3 C_*.
\]
For the continuous representatives of radial homogeneous-energy functions at every (R>0),
\[
\boxed{\quad
R^{5/2}|\mathcal N_H(u)(R)-\mathcal N_H(v)(R)|
\le C_{\rm pt}\,E^6D.\quad}\tag{RH1}
\]
In particular this estimate is a *producer from the actual inverse-square quartic Hartree map*, not an assumed pointwise source envelope. The power (R^{-5/2}) is critical under (w_\lambda(x)=\lambda^{1/2}w(\lambda x)).

### Complete radial/Hölder derivation

The fundamental theorem of calculus with the physical (4\pi r^2dr) measure gives
\[
|w(R)|\le c_*R^{-1/2}\|\nabla w\|_2.\tag{RH2}
\]
Fix (x\in\mathbb R^3), (|x|=R>0), and split the *actual* potential integral into (|x-y|\le R/2) and its complement. On the near portion (|y|\ge R/2), while
\[
\int_{|z|\le R/2}|z|^{-2}dz=2\pi R,
\qquad
\|\mathbf1_{|z|>R/2}|z|^{-2}\|_3
=\left(\frac{32\pi}{3}\right)^{1/3}R^{-1}.
\]
Using (RH2) on the near region, and Hölder plus Sobolev on the far region, yields
\[
\big|(|x|^{-2}*|v|^4)(x)\big|
\le C_* R^{-1}\|\nabla v\|_2^4.\tag{RH3}
\]
The genuine quartic-density difference satisfies
\[
\begin{aligned}
\big\||u|^4-|v|^4\big\|_{3/2}
&\le4S^4 E^3D,\\
\big||u(y)|^4-|v(y)|^4\big|
&\le4c_*^4 E^3D |y|^{-2}\qquad (y\ne0).
\end{aligned}
\]
The same near/far split therefore gives
\[
\big|\big(|x|^{-2}*(|u|^4-|v|^4)\big)(x)\big|
\le4C_* R^{-1}E^3D.\tag{RH4}
\]
Indeed the near-region numerical constant in (RH3) is
(4c_*^4\cdot2\pi=1/(2\pi)).
Finally, the complex cubic factor satisfies
\[
\big||u|^2u-|v|^2v\big|(R)
\le3c_*^3 E^2D R^{-3/2}.\tag{RH5}
\]
Insert (RH3)--(RH5) into the **exact** decomposition
\[
\mathcal N_H(u)-\mathcal N_H(v)
=\kappa_H\big[\big(K*(|u|^4-|v|^4)\big)|u|^2u
 +(K*|v|^4)(|u|^2u-|v|^2v)\big].
\]
The coefficients (4+3=7) give (RH1). All integrals converge at each (R>0): the near kernel is locally integrable and radial (\dot H^1) representatives are bounded on compact positive-radius annuli; the far part is Hölder-integrable. Smooth radial approximation proves the same inequality for the indicated energy class without imposing an independent smooth source.

## B. Exact original singular Cramer coefficient, no physical shell hypothesis

Use the *actual* origin-normalized Kummer pair and Wronskian already Lean certified in
`HBL/KummerOriginGreen/GreenBridge.lean`:
\[
Y_K(r)=K.y(r)/r,\qquad W_K(r)=r^{-2}e^{-ir^2/4}.
\]
Take (a>0), (0<L<aB), (r_0=L/a), and the *true* scaled nonlocal increment
(F_a(r)=a^2\{\mathcal N_H(u)-\mathcal N_H(v)\}(ar)).
For (C_Y=\sup_{r\in[r_0,B]}|K.y(r)|<\infty), the precise change of variables is
\[
\mathcal C_B^K[F_a]
=\int_{L}^{aB}K.y(y/a)e^{iy^2/(4a^2)}
\,y\,\{\mathcal N_H(u)-\mathcal N_H(v)\}(y)\,dy.
\]
Apply (RH1), with (y|\delta\mathcal N(y)|\le C_{\rm pt}E^6D\,y^{-3/2}), to conclude
\[
\boxed{
|\mathcal C_B^K[F_a]|
\le2C_YC_{\rm pt}E^6D
\big(L^{-1/2}-(aB)^{-1/2}\big)
\le2C_YC_{\rm pt}E^6D L^{-1/2}.}\tag{RH6}
\]
**Unlike the earlier supported-shell estimate (SB2), this requires neither compact support of (u-v) nor a volume (V_{L,h}) bound.** It still requires the actual physical Cramer starting radius (ar_0=L>0). It controls precisely the nonlinear *feedback increment*, not the complete PDE forcing.

For the same fixed basis, (a,u,v), if the physical integration interval endpoints move with (L_j,T_j\ge L_*>0), with (L_j<T_j), then the weighted integrand gives
\[
\boxed{
|\mathcal C(L_1,T_1)-\mathcal C(L_2,T_2)|
\le C_Y C_{\rm pt}E^6D\,L_*^{-3/2}
\big(|L_1-L_2|+|T_1-T_2|\big),}\tag{RH7}
\]
where (C_Y) uniformly bounds (|K.y(y/a)|) throughout both intervals and
\(\mathcal C(L,T)=\int_L^T K.y(y/a)e^{iy^2/(4a^2)}y\delta\mathcal N(y)dy\).
This is the **nonlinear endpoint** Lipschitz bridge, without a separately assumed source trace. For a common physical interval, two pairs ((u_i,v_i)) admit the analogous fixed-basis Lipschitz estimate by twice applying (RH6) to (\mathcal N_H(u_1)-\mathcal N_H(u_2)) and (\mathcal N_H(v_1)-\mathcal N_H(v_2)).

## C. Exact scope and unproved original prerequisites

- (RH1)--(RH7) are proved here only on paper; no new strict `#check`, `#print axioms` or GitHub Actions Success is asserted.
- The estimates apply directly to the **genuine radial nonlocal increment** and solve the **nonlinear part** of the singular-Cramer left-radius-loss issue at positive physical (L). They do **not** control unrelated linear/time derivative sources, the full spectral-corrected four-region residual, or the source after differentiating in physical time.
- A fixed (C_Y) is not a uniform moving-Kummer parameter estimate; basis derivatives and the actual two-real-speed Jacobian still have to be produced from the same orbit. (RH7) is only moving-endpoint Lipschitz with fixed (a,K,u,v).
- To derive a time gain, one must quantify the *actual* energy distance (D(s)), the physical (L(s)), and all other residual components from the Hartree dynamics. No time-order or Type-II exponent is postulated.

**Counting:** retained revised original paper remains **11/13**. §2.13 and the final dynamic Type-II theorem are not certified.


## D. Sharpness: no improved physical-radius power from radial energy alone

This optimality statement is **only for energy-class inputs**; it is not a counterexample to the selected Hartree PDE orbit. Choose any nonzero real nonnegative \(\phi\in C_c^\infty(\mathbb R^3)\) radial, supported where \(1<|x|<2\). For \(L\to\infty\), set
\[
u_L(x)=L^{-1/2}\phi(x/L),\qquad v_L=0,\qquad
a_L=L^3,\quad r_{0,L}=L/a_L=L^{-2},\quad B=1.
\]
Then \(\|\nabla u_L\|_2=\|\nabla\phi\|_2\) and exact Hartree critical scaling gives
\[
\mathcal N_H(u_L)(L\rho)=L^{-5/2}\mathcal N_H(\phi)(\rho).
\]
For a fixed original origin-normalized Kummer mode with \(K.y(0)=1\), the **genuine** singular Cramer integral is
\[
\begin{aligned}
\mathcal C_B^K[a_L^2\mathcal N_H(u_L)(a_L\,\cdot)]
&=L^{-1/2}\int_1^2 \rho\,\mathcal N_H(\phi)(\rho)
 K.y(\rho/L^2)e^{i\rho^2/(4L^4)}\,d\rho\\
&=L^{-1/2}(M_\phi+o(1)),\qquad
M_\phi=\int_1^2\rho\,\mathcal N_H(\phi)(\rho)\,d\rho>0.
\end{aligned}\tag{RH8}
\]
The support of \(\mathcal N_H(u_L)\) agrees with that of \(u_L\) because the nonlinearity contains the local factor \(|u_L|^2u_L\); the convolution potential itself is nonlocal. Uniform convergence of the two smooth fixed-basis factors on \(1\le\rho\le2\) proves the limit. Thus the \(L^{-1/2}\) factor in (RH6) is **sharp in general** and no \(o(L^{-1/2})\) nonlinear Cramer gain follows solely from uniform radial \(\dot H^1\) norms, even for genuine inverse-square quartic Hartree nonlinearities.

Consequently any additional *time* gain required by the original §2.13 must use **actual PDE-induced smallness or cancellation** of the selected correction (or a stronger structural restriction), not the radial energy estimate or large overlap radius by itself. This constructed family is not asserted to solve Hartree evolution and supplies neither a forbidden rate assumption nor a dynamical obstruction.
