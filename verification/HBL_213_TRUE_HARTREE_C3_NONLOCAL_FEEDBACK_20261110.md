# HBL §2.13 — global original-Hartree feedback of the exact third-jet shell repair

10 November 2026 (Pacific time). **Paper proof; not a new Lean theorem.** Starting point: the physically supported third-jet Hermite correction from `HBL_213_INTERFACE_REGULARITY_GATE_20261111.md`. Revised original 13 environments: **11/13**, unchanged. The present result gives the **entire nonlocal** feedback in the critical energy-dual topology, with no independently assumed envelope or positive time power. It does **not** prove the stronger Hessian–Morawetz-dual / differentiated source estimate or retain the old two-speed selector.

## 1. Original nonlocal map; critical HLS estimate

For complex `u` on `R^3`, put
\[
K(x)=|x|^{-2},\quad V[u]=\kappa_H K*|u|^4,\quad
\mathcal N_H(u)=V[u]|u|^2u,\qquad \kappa_H>0.
\]
This is the literal inverse-square **quartic-density** Hartree interaction, not a local NLS nonlinearity. For \(u,v\in\dot H^1(\mathbb R^3;\mathbb C)\), let \(A=\|u\|_6+\|v\|_6\).
The Hardy–Littlewood–Sobolev inequality for the Riesz potential of order one gives
\[
 \|K*f\|_3\le C_{\rm HLS}\|f\|_{3/2}.
\]
Pointwise polynomial differences and Hölder yield
\[
 \||u|^4-|v|^4\|_{3/2}\le4A^3\|u-v\|_6,\qquad
 \||u|^2u-|v|^2v\|_2\le3A^2\|u-v\|_6.
\]
Decompose **before** taking norms:
\[
\begin{aligned}
 \mathcal N_H(u)-\mathcal N_H(v)
 &=\big(V[u]-V[v]\big)|u|^2u\\
 &\quad+V[v]\big(|u|^2u-|v|^2v\big).
\end{aligned}
\]
The first product has exponents \((3,2)\) and the second has the same exponents. Therefore
\[
\boxed{\
\|\mathcal N_H(u)-\mathcal N_H(v)\|_{6/5}
 \le 7\kappa_H C_{\rm HLS} A^6\|u-v\|_6.
\ }\tag{NF1}
\]
If \(S\) denotes the constant in \(\|f\|_6\le S\|\nabla f\|_2\), duality supplies
\[
\boxed{\
\|\mathcal N_H(u)-\mathcal N_H(v)\|_{\dot H^{-1}}
 \le 7\kappa_H C_{\rm HLS}S^8
 (\|\nabla u\|_2+\|\nabla v\|_2)^6
 \|\nabla(u-v)\|_2.
\ }\tag{NF2}
\]
The derivative of this seventh-degree real polynomial mapping obeys the corresponding second-difference estimate (by expanding its seven slots, applying the same HLS and Hölder inequalities):
\[
\begin{split}
\|\{\mathcal N_H(U_1+P_1)-\mathcal N_H(U_1)\}
  -\{\mathcal N_H(U_2+P_2)-\mathcal N_H(U_2)\}\|_{\dot H^{-1}}
\le C_{\kappa,HLS,S}\big[&
 (E+D)^6\|\nabla(P_1-P_2)\|_2\\
 &+(E+D)^5D\|\nabla(U_1-U_2)\|_2\big],
\end{split}\tag{NF3}
\]
provided \(\|\nabla U_i\|_2\le E\), \(\|\nabla P_i\|_2\le D\).
Unlike an independently assumed parameter envelope, (NF3) is a direct **nonlinear operator estimate**; actual parameter regularity of the repaired packet is still to be derived from its formulas.

## 2. Source-produced physical shell repair and its precise Sobolev costs

At one real radius \(L>0\), choose \(h>0\) with its repair shell disjoint from the other two physical interfaces. Set \(\xi=(r-L)/h\) and
\[
 \phi_2(\xi)=\frac12\xi^2(1-\xi)^4(1+4\xi),\qquad
 \phi_3(\xi)=\frac16\xi^3(1-\xi)^4.
\]
For **actual** (complex) curvature and third-jet discrepancies \(d_2,d_3\) taken from the SAME Fredholm/Kummer packet, define
\[
 P(r)=\begin{cases}
 h^2d_2\phi_2((r-L)/h)+h^3d_3\phi_3((r-L)/h),&L\le r\le L+h,\\
 0,&\text{otherwise}.
 \end{cases}
\]
Define the exact shell volume and fixed numerical kernel constants by
\[
 \mathsf V_{L,h}=\frac{4\pi}{3}((L+h)^3-L^3),\quad
 M_j=\max_{0\le\xi\le1}|\phi_j(\xi)|,\quad
 M'_j=\max_{0\le\xi\le1}|\phi'_j(\xi)| .
\]
Since \(P=P_r=0\) at both endpoints of its support, its weak gradient has no interface measure. Direct calculation, **including physical radial volume**, yields
\[
 \boxed{\
 \|P\|_{L^6(\mathbb R^3)}
 \le \mathsf V_{L,h}^{1/6}\big(h^2|d_2|M_2+h^3|d_3|M_3\big),
 \ }\tag{NF4}
\]
\[
 \boxed{\
 \|\nabla P\|_{L^2(\mathbb R^3)}
 \le \mathsf V_{L,h}^{1/2}
    \big(h|d_2|M'_2+h^2|d_3|M'_3\big).
 \ }\tag{NF5}
\]
Substituting \(v=U\), \(u=U+P\) into (NF2) gives a genuine **global** bound on the perturbed quartic Hartree convolution, even far outside the shell:
\[
\boxed{\
\|\mathcal N_H(U+P)-\mathcal N_H(U)\|_{\dot H^{-1}}
\le C(2\|\nabla U\|_2+\|\nabla P\|_2)^6\|\nabla P\|_2.
\ }\tag{NF6}
\]
Here \(C=7\kappa_H C_{\rm HLS}S^8\); no claim of compact support of the convolution difference is made. Moreover
\[
 \|\Delta P\|_{\dot H^{-1}}\le\|\nabla P\|_2.
\]
For bounded \(L,h,d_2,d_3\), translating the center at fixed \(h,d_j\) gives the derivative identity \(\partial_LP=-P_r\) in distributions and the quantitative bound
\[
 \|\partial_LP\|_{\dot H^1}
 \le\mathsf V_{L,h}^{1/2}
   (|d_2|M''_2+h|d_3|M''_3),\quad
 M''_j=\max_{[0,1]}|\phi_j''|.
\tag{NF7}
\]
Endpoint conditions are essential here; all physical \(L,h\)-variation of the radial weights is retained through \(\mathsf V_{L,h}\).

## 3. Exact moving-source ledger and acceptance boundary

If \(L,h,d_2,d_3\) depend differentiably on time and the evaluated \(\phi_j\) are taken at \(\xi=(r-L)/h\), then **inside** the moving repair shell,
\[
\begin{aligned}
 P_t={}&h^2\dot d_2\phi_2+h^3\dot d_3\phi_3\\
 &+\dot h\big[h d_2(2\phi_2-\xi\phi_2')
 +h^2d_3(3\phi_3-\xi\phi_3')\big]\\
 &-\dot L\big[h d_2\phi_2'+h^2d_3\phi_3'\big].
\end{aligned}\tag{NF8}
\]
There are no moving-interface delta masses in \(P_t\) because \(P\) vanishes at its endpoints. For the **same original** renormalized residual \(\mathcal R\),
\[
\boxed{\
 \mathcal R(U+P)-\mathcal R(U)
 =iP_t+\Delta_rP+ib\Lambda P+\omega P+
   \{\mathcal N_H(U+P)-\mathcal N_H(U)\}.
\ }\tag{NF9}
\]
This is an exact nonlinear identity, not a positive time-power estimate.

**What has genuinely been controlled:** (NF6) proves the *full nonlocal, all-space* feedback of the C3 repair in \(\dot H^{-1}\) from the actual repair jets and physical shell width; (NF3) shows the operator-level two-state Lipschitz law, contingent only on finite energy. Unlike the old telescope, this is a genuine norm inequality.

**What has NOT been controlled:** the actual same-PDE jet bounds \(d_2,d_3,\dot d_2,\dot d_3\), the moving \(L_t,h_t\) and Kummer-basis derivatives, the stronger differentiated Hessian–Morawetz source norm, the continuity of the *particular outgoing Cramer obstruction functional* on this \(\dot H^{-1}\) topology, or the response of the uniquely selected two real speeds to the global changed convolution. The physical four-region Hartree orbit, nonlinear finite-layer recursion, time-positive/parameter-Lipschitz full residual and PDE-derived Type-II rate are all OPEN. There is no new exact Lean #check/#print-axioms certificate for (NF1)–(NF9). **Original count 11/13.**
