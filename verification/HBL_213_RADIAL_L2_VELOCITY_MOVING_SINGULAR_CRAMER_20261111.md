# HBL §2.13: genuine Hartree singular-Cramer moving source with only radial L² time velocity

11 November 2026. **Complete paper-level calculation, NOT a Lean certificate.** Original revised acceptance **11/13**. This note improves the source term in the previously recorded exact moving-endpoint formula (MT4) without asserting a complete PDE residual gain, time rate, or independent forcing envelope.

## 1. Mixed radial six-energy/one-L² estimate

Throughout, all functions are radial on \(\mathbb R^3\), complex-valued unless explicitly real. Write \(K(x)=|x|^{-2}\), \(\|f\|_6\le S\|\nabla f\|_2\), \(c_*=(4\pi)^{-1/2}\), and
\[
 C_*=\frac1{2\pi}+\Bigl(\frac{32\pi}{3}\Bigr)^{1/3}S^4,\quad
 J_*=\int_{1/2}^2 \log^2\frac{1+t}{|1-t|}\,dt<\infty,\quad
 C_{\rm rad}=4S^3+2^{3/2}\sqrt\pi\,c_*^3\sqrt{J_*}.
\]
The logarithmic singularity at \(t=1\) is square-integrable. For radial \(h_1,h_2,h_3\in\dot H^1\), \(w\in L^2\), prove the **actual inverse-square convolution** bound
\[
\boxed{\quad
\sup_{R>0}R^2
\big|K*(h_1\overline{h_2}h_3w)\big|(R)
\le C_{\rm rad}\|w\|_2\prod_{j=1}^3\|\nabla h_j\|_2.
\quad}\tag{RV1}
\]
The same inequality holds after conjugating any subset of the factors.

**Proof.** Fix \(|x|=R\) and decompose the actual convolution in the *source radius* \(\rho=|y|\): \(\rho\notin[R/2,2R]\) and \(\rho\in[R/2,2R]\). On the complement, \(|x-y|\ge R/2\), so Hölder with exponents \((6,6,6,2)\) gives
\[
 \left|\int_{\rho\notin[R/2,2R]}|x-y|^{-2}
 h_1\bar h_2h_3w\,dy\right|
 \le4R^{-2}S^3\|w\|_2\prod_{j=1}^3\|\nabla h_j\|_2.
\]
On the near radial annulus, *integrate angles before applying Cauchy–Schwarz*:
\[
 \int_{S^2}\frac{d\omega}{|Re_3-\rho\omega|^2}
 =\frac{2\pi}{R\rho}
    \log\frac{R+\rho}{|R-\rho|}\quad(R\ne\rho).
\]
The radial Strauss estimate \(|h_j(\rho)|\le c_*\rho^{-1/2}\|\nabla h_j\|_2\), valid for a.e. \(\rho>0\), gives
\[
\begin{aligned}
 |V_{\rm ann}(R)|
 &\le \frac{2\pi}{R}c_*^3(R/2)^{-3/2}
 \prod_{j=1}^3\|\nabla h_j\|_2
 \int_{R/2}^{2R}\rho|w(\rho)|
       \log\frac{R+\rho}{|R-\rho|}\,d\rho\\
 &\le \frac{2\pi}{R}c_*^3(2/R)^{3/2}
 \prod_{j=1}^3\|\nabla h_j\|_2
 \frac{\|w\|_2}{\sqrt{4\pi}}\sqrt{RJ_*}\\
 &=2^{3/2}\sqrt\pi\,c_*^3\sqrt{J_*}\,
 R^{-2}\|w\|_2\prod_{j=1}^3\|\nabla h_j\|_2.
\end{aligned}
\]
Adding both regions proves (RV1). The angular integration is essential: a naive 3D \(L^2\) bound on the pointwise kernel \(|x-y|^{-2}\) would fail locally.

## 2. Weighted Cramer functional with a single L² factor

Write the genuine seven-real-linear Hartree product
\[
 \mathfrak T(a_1,\ldots,a_7)(R)
 =\kappa_H
 [K*(a_1\bar a_2a_3\bar a_4)](R)
 a_5(R)\bar a_6(R)a_7(R).
\]
Fix \(0<L<T\), a bounded complex weight \(B(R)\) with \(\sup_{[L,T]}|B|\le A_0\), and let exactly one of the seven radial entries \(a_j=w\in L^2\), the other six lie in \(\dot H^1\). Define
\[
 C_{\rm wk}=
 \max\left\{
 \frac{2}{3}c_*^3 C_{\rm rad},
 \frac{c_*^2 C_*}{\sqrt{12\pi}}
 \right\}.
\]
Then the genuine singular-Cramer integral satisfies
\[
\boxed{\quad
 \left|\int_L^T R B(R)\,
        \mathfrak T(a_1,\ldots,a_7)(R)\,dR\right|
 \le \kappa_H A_0 C_{\rm wk}L^{-3/2}
 \|w\|_2\prod_{i\ne j}\|\nabla a_i\|_2.
\quad}\tag{RV2}
\]

**Proof, convolution slot.** When \(j\in\{1,2,3,4\}\), (RV1) bounds the genuine convolution by \(C_{\rm rad}R^{-2}\|w\|_2\prod_{i\le4,i\ne j}\|\nabla a_i\|_2\). The remaining three radial-energy factors contribute \(c_*^3R^{-3/2}\prod_{i=5}^7\|\nabla a_i\|_2\). Consequently the weighted radial integrand is at most a constant times \(R^{-5/2}\), and \(\int_L^T R^{-5/2}dR\le(2/3)L^{-3/2}\).

**Proof, exterior cubic slot.** When \(j\in\{5,6,7\}\), the *actual* quartic convolution bound (RH3) from the previous radial note is \(|K*(a_1\bar a_2a_3\bar a_4)|(R)\le C_*R^{-1}\prod_{i\le4}\|\nabla a_i\|_2\). The two remaining exterior energy factors contribute \(c_*^2R^{-1}\); the weighted integrand is then bounded by \(C_*c_*^2R^{-1}|w(R)|\). The radial physical measure yields the exact Cauchy–Schwarz estimate
\[
 \int_L^T R^{-1}|w(R)|\,dR
 \le\frac{\|w\|_2}{\sqrt{4\pi}}
      \left(\int_L^\infty R^{-4}\,dR\right)^{1/2}
 =\frac{\|w\|_2}{\sqrt{12\pi}}L^{-3/2}.
\]
These two cases exhaust all seven factors, and no independent source envelope has been used.

## 3. Genuine time differentiation in the L² velocity topology

Assume \(U,V\) are smooth radial energy fields on the swept interval, differentiable in time with \(U_s,V_s\in L^2_{\rm rad}\). No \(\dot H^1\) bound on their time derivatives is needed for the following *integrated* assertion. Put
\[
\begin{gathered}
f(s,R)=\mathcal N_H(U(s))(R)-\mathcal N_H(V(s))(R),\\
 E=\|\nabla U\|_2+\|\nabla V\|_2,\quad
 D=\|\nabla(U-V)\|_2,\\
 V_2=\|U_s\|_2+\|V_s\|_2,\quad
 D_2=\|U_s-V_s\|_2 .
\end{gathered}
\]
Expanding the actual seven-linear derivative, then telescoping the six remaining positions (using the real-multilinearity, including conjugate positions), and applying (RV2) to each term gives
\[
\boxed{\quad
\left|\int_L^T R B(R)\partial_sf(s,R)\,dR\right|
\le7\kappa_H A_0 C_{\rm wk} L^{-3/2}
 \left(E^6D_2+6E^5V_2D\right).
\quad}\tag{RV3}
\]
The assertion first holds for smooth fields, and extends by density whenever this weighted functional is differentiable in the indicated mixed topology. It is not a claim that \(\partial_s f\) has the pointwise envelope of (MT2) when the time velocities lie merely in \(L^2\).

For the *same genuine moving Kummer singular coefficient* as (MT3),
\[
 \mathcal C(s)=\int_{L(s)}^{T(s)}
 y\,k(s,y/a(s))e^{iy^2/(4a(s)^2)}f(s,y)\,dy ,
\]
let \(A_0,A_t,A_r\) be the **observed** basis suprema already defined in (MT5), not assumed uniform across all physical parameters; let \(C_0=\kappa_Hc_*^3C_*\). The exact Leibniz identity (MT4), (RV3) and the genuine pointwise feedback bound (MT2), applied only where valid, give
\[
\boxed{
\begin{aligned}
|\mathcal C'(s)|\le {}&
 7C_0 A_0E^6D\bigl(|L'|L^{-3/2}+|T'|T^{-3/2}\bigr)\\
&+7\kappa_H A_0C_{\rm wk}L^{-3/2}
  \bigl(E^6D_2+6E^5V_2D\bigr)\\
&+14C_0E^6DL^{-1/2}
 \left[A_t+\left|\frac{a'}a\right|
       \left(A_r+\frac{T^2}{2a^2}A_0\right)\right].
\end{aligned}}\tag{RV4}
\]
**Compared with (MT5), (RV4) replaces strong \(\dot H^1\)-time-velocity requirements by physical \(L^2\) velocities for the genuinely differentiated nonlinear source and gives an additional \(L^{-1}\) factor on that term.** Moving endpoint and moving basis contributions retain their explicit previous budgets.

## 4. Scaling check, acceptance boundary, and missing PDE producer

The \(L^{-3/2}\) exponent in (RV2) is generally sharp under only radial energy and \(L^2\)-velocity control. Choose real nonnegative radial \(0\ne\phi\in C_c^\infty(\{1<|x|<2\})\), and at physical scale \(L\) use
\[
 U_L(x)=L^{-1/2}\phi(x/L),\qquad
 W_L(x)=L^{-3/2}\phi(x/L),\qquad a_L=L^3.
\]
The energy norm of \(U_L\) and \(L^2\) norm of \(W_L\) are scale-invariant, while
\[
 \int_L^{2L}R\,
    \mathcal N_H'(U_L)[W_L](R)\,dR
 =7L^{-3/2}\int_1^2 \rho\,\mathcal N_H(\phi)(\rho)\,d\rho>0.
\]
The same leading term persists with the genuine origin-normalized Kummer factor \(k(\rho/L^2)e^{i\rho^2/(4L^4)}\to1\) uniformly on \([1,2]\). Thus no stronger universal radius power follows solely from those norms.

The remaining **actual PDE obligations** are to produce \(D(s),D_2(s),V_2(s)\) on the selected four-piece trajectory, control \((a'/a,L',T',A_t,A_r)\) and the two-real-speed Jacobian from the same source, and prove positive time order and parameter Lipschitz for *all* linear, interface and nonlinear residuals in the required strong source topology. The C²/C³ interface regularity obstruction is not removed by an integrated Green coefficient estimate. Neither a time exponent nor an II-type blowup rate is an input or conclusion here.

**Formal boundary:** (RV1)–(RV4) are paper proofs, not checked Lean declarations. They do not supersede the original strict CI for four-piece \(C^1\) joins or telescoping, do not certify the genuine time residual, and do not increase the **11/13** original-environment acceptance.
