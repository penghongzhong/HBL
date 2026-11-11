# HBL §2.13: exact moving singular-Cramer derivative of the *actual* critical Hartree feedback

**11 November 2026. Mathematical proof, not a Lean-certified theorem.** The 13 retained original environments remain **11/13**. The result concerns the nonlinear feedback increment only; it does not assert the required full-PDE residual time gain.

## 1. A seven-linear radial Hartree bound and its true time derivative

Set
\[
\mathcal N_H(w)=\kappa_H\,(|x|^{-2}*|w|^4)|w|^2w,
\qquad c_*=(4\pi)^{-1/2},\qquad
C_*=\frac1{2\pi}+\left(\frac{32\pi}{3}\right)^{1/3}S^4,
\quad C_0=\kappa_Hc_*^3C_* ,
\]
where \(\|g\|_6\le S\|\nabla g\|_2\). For radial complex-energy functions define the real-multilinear map
\[
\mathfrak T(a_1,\ldots,a_7)(x)
=\kappa_H\left[|x|^{-2}*(a_1\bar a_2 a_3\bar a_4)\right](x)
 a_5(x)\bar a_6(x)a_7(x).
\]
The same near/far convolution split as (RH2)--(RH4) in the radial pointwise Cramer note, now applied to distinct factors, gives
\[
\boxed{\quad \sup_{R>0}R^{5/2}|\mathfrak T(a_1,\ldots,a_7)(R)|
 \le C_0\prod_{j=1}^{7}\|\nabla a_j\|_2.\quad}\tag{MT1}
\]
Indeed for \(|x|=R\), on \(|x-y|\le R/2\) all four inner factors have
\(|a_j(y)|\le c_* (R/2)^{-1/2}\|\nabla a_j\|_2\), and the kernel integral equals \(2\pi R\).
The near convolution constant is \(8\pi c_*^4=1/(2\pi)\). On the complement, Holder's inequality with the kernel in \(L^3\) and the product in \(L^{3/2}\) gives
\(\big(32\pi/3\big)^{1/3}S^4R^{-1}\prod_{1}^{4}\|\nabla a_j\|_2\).
The outer three factors contribute \(c_*^3R^{-3/2}\prod_{5}^{7}\|\nabla a_j\|_2\).
The same proof works with any pattern of complex conjugation.

Let \(U,V\in C^1(J;\dot H^1_{\rm rad}(\mathbb R^3;\mathbb C))\), with differentiation in the **strong energy topology**, and write
\[
f(s,R)=\mathcal N_H(U(s))(R)-\mathcal N_H(V(s))(R),\quad
E=\|\nabla U\|_2+\|\nabla V\|_2,\quad D=\|\nabla(U-V)\|_2,
\]
\[
E_1=\|\nabla U_s\|_2+\|\nabla V_s\|_2,\qquad
D_1=\|\nabla(U_s-V_s)\|_2 .
\]
The continuous seven-linear mapping (MT1) justifies differentiation of the *actual* convolution in the weighted pointwise topology. Expanding seven real-linear derivatives, then telescoping the six remaining factors in each derivative summand, yields the source-produced estimates
\[
\boxed{\quad
\sup_{R>0}R^{5/2}|f(s,R)|\le 7C_0E^6D,\qquad
\sup_{R>0}R^{5/2}|\partial_sf(s,R)|
\le C_0\big(7E^6D_1+42E^5E_1D\big).
\quad}\tag{MT2}
\]
The factors 7 and 42 count the actual cubic/quartic Hartree slots, not abstract source envelopes.

## 2. The exact moving-basis/endpoint derivative in physical coordinates

Let \(a,L,T\in C^1(J)\), with \(a>0\), \(0<L<T\); denote the *origin-normalized* singular Kummer numerator by \(k(s,r)=K_s.y(r)\). Assume \(k\in C^1\) on the swept compact Kummer domain. The actual Green source is
\(F_a(s,r)=a(s)^2f(s,a(s)r)\), the original Wronskian is
\(W_K(r)=r^{-2}e^{-ir^2/4}\), and \(Y_K(s,r)=k(s,r)/r\).
By an **exact** physical change of variables,
\[
\mathcal C(s)
=\int_{L(s)/a(s)}^{T(s)/a(s)}
  \frac{Y_K(s,r)F_a(s,r)}{W_K(r)}dr
=\int_{L(s)}^{T(s)}
  y\,k(s,y/a(s))e^{iy^2/(4a(s)^2)} f(s,y)\,dy .
\tag{MT3}
\]
In particular no spurious explicit derivative of an \(a^2\) source prefactor survives. With \(z=y/a(s)\), the literal Leibniz formula is
\[
\begin{split}
\mathcal C'(s)={}&T'T\,B(s,T)f(s,T)-L'L\,B(s,L)f(s,L)\\
&+\int_L^T yB(s,y)\partial_sf(s,y)\,dy\\
&+\int_L^T ye^{iy^2/(4a^2)}f(s,y)
\left[
(\partial_sk)(s,z)-\frac{a'}a z(\partial_rk)(s,z)
-i\frac{a'}a\frac{y^2}{2a^2}k(s,z)
\right]dy ,
\end{split}\tag{MT4}
\]
where \(B(s,y)=k(s,y/a)e^{iy^2/(4a^2)}\); \(\partial_sk\) means the derivative at **fixed Kummer radius**.

Suppose on the whole interval \(y\in[L,T]\) one has the observed basis-size quantities
\[
A_0=\sup|k(s,y/a)|,\quad
A_t=\sup|(\partial_sk)(s,y/a)|,\quad
A_r=\sup|(y/a)(\partial_rk)(s,y/a)|.
\]
They are definitions, **not assertions of uniformity in the moving parameters**. Directly from (MT2)--(MT4),
\[
\boxed{
\begin{aligned}
|\mathcal C'(s)|\le {}&
7C_0A_0E^6D\big(|L'|L^{-3/2}+|T'|T^{-3/2}\big)\\
&+2C_0L^{-1/2}A_0\big(7E^6D_1+42E^5E_1D\big)\\
&+14C_0L^{-1/2}E^6D
\left[A_t+\left|\frac{a'}a\right|
\left(A_r+\frac{T^2}{2a^2}A_0\right)\right].
\end{aligned}}\tag{MT5}
\]
All constants are explicit, and there is no negative power of the Kummer left radius \(r_0=L/a\). The integral \(\int_L^T y^{-3/2}dy\le2L^{-1/2}\) supplies the only bulk spatial factor. If the displayed right-hand side is integrable in \(s\), the fundamental theorem of calculus immediately gives a corresponding time-Lipschitz bound for \(\mathcal C\).

## 3. Remaining real-PDE gates

(MT5) replaces an **independent assumption on** \(\partial_s[\mathcal N_H(U)-\mathcal N_H(V)]\) by explicit strong-energy velocities of the *same two fields*. However the actual selected four-piece Hartree orbit has NOT yet been shown to satisfy the required bounds on \(E_1,D_1,L',T',a'/a,A_t,A_r\) at a positive time order; in particular \(\dot H^1\)-control of \(U_s\) is stronger than energy control of \(U\). The full selected-source residual also contains linear, time-transport, and interface terms beyond \(f\), and the two real compatibility speeds must be recomputed after any splice. The derivative estimate cannot be read as proof of an \(s^{-9/4}\) residual, parameter Lipschitz, finite profile recursion, or dynamic Type-II rate.

**Exact formal boundary:** paper-only (MT1)--(MT5); no fresh Lean compilation, #check or #print axioms, and **11/13** retained original environments.
