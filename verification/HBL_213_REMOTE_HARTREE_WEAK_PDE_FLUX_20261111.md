# §2.13 — genuine Hartree PDE weak-flux repair of the remote moving potential

11 November 2026. **Paper proof only: original revised environments 11/13.** This supplies a new route around the unproved high-regularity quantity \(\mathfrak M(\Delta z+\mathcal N_H(z))^{1/4}\) in IM10–IM12 of HBL_213_REMOTE_INVERSE_MOMENT_RESCUE_20261111.md. It is **not** the untruncated Hartree source, a parameter-uniform finite profile, a time-positive residual estimate, or Lean acceptance.

## 1. Same physical Hartree PDE, no invented source velocity

Use the actual three-dimensional critical inverse-square quartic Hartree equation
\[
 iz_t+\Delta z+\mathcal N_H(z)=0,\qquad
 \mathcal N_H(z)=\kappa_H(|x|^{-2}*|z|^4)|z|^2z,\quad \kappa_H\in\mathbb R.
\]
For positive differentiable \(\ell(s)\), \(t_s=\ell^2\), \(\ell_s=-b\ell\), define
\(Z(s,x)=\sqrt{\ell(s)}z(t(s),\ell(s)x)\). The exact critical scaling yields
\[
 Z_s=i[\Delta Z+\mathcal N_H(Z)]-b\Lambda Z,\qquad
 \Lambda Z=\tfrac12 Z+x\cdot\nabla Z. \tag{WF1}
\]
Let \(V=V(s,x)\) be a real smooth radial reference profile, *not* presumed time-independent, and put
\(U=V+Z\), \(\rho=|U|^4-|V|^4\). No equation for \(U\), zero PDE residual, or temporal decay is assumed.

## 2. Exact separated radial kernel and constants

Let \(L(s)>0\), \(R(s)=\theta L(s)\), \(3/4\le\theta\le1\), and \(\chi\in C_c^1([0,\infty))\) with support in \([0,1/3]\), \(|\chi|\le1\), \(C_\chi=\|\chi'\|_\infty\). Set
\[
 K_R(q)=\frac{1}{2Rq}\log\frac{R+q}{R-q}
       =R^{-2}\sum_{j=0}^{\infty}\frac{(q/R)^{2j}}{2j+1},
 \quad 0\le q<R,\qquad K_R(0)=R^{-2}.
\]
The genuinely truncated three-dimensional Hartree potential difference is
\[
 Q_\chi(s,R)=4\pi\int_0^\infty q^2
      \chi(q/L(s))K_R(q)\rho(s,q)\,dq
 =\int_{\mathbb R^3}w_{R,L}(|x|)\rho(s,x)\,dx,
 \quad w_{R,L}(q)=\chi(q/L)K_R(q). \tag{WF2}
\]
For \(0\le q\le L/3\) and \(3L/4\le R\le L\), \(q/R\le4/9\). Direct positive-series estimates (not a volume-moment substitution) give
\[
 \|w\|_\infty\le W_0=\frac{144}{65L^2},\quad
 \|\partial_qw\|_\infty\le W_1=
   \frac{256+432C_\chi}{195L^3},\quad
 \|\partial_Rw\|_\infty\le W_R=\frac{384}{65L^3}. \tag{WF3}
\]
Indeed \(|K_R|\le[R^2(1-t^2)]^{-1}\),
\(|\partial_q K_R|\le R^{-3}t/(1-t^2)\), and
\(|\partial_R K_R|\le2R^{-3}/(1-t^2)\), with \(t=q/R\).
These inequalities use the true separated physical kernel and have no factor \(r_0^{-1}\).

## 3. Weighted weak PDE identity removes two spatial derivatives

Write \(\Phi=|U|^2\overline U\) and \(\Omega_L=B_{L/3}(0)\). For a classical smooth radial Hartree trajectory, differentiate WF2 along \(R(s)\), use WF1 and integrate by parts *before taking absolute values*. The radial \(2q^{-1}Z_q\) is included automatically by integration in the \(4\pi q^2dq\) measure:
\[
\begin{aligned}
\frac{d}{ds}Q_\chi(s,R(s))
={}&\int_{\mathbb R^3}
       [\partial_s w|_{R\ {\rm fixed}}+R'\partial_Rw]\,\rho\,dx\\
&-4\Re\int_{\mathbb R^3}
    i\,\nabla(w\Phi)\cdot\nabla Z\,dx
 +4\Re\int_{\mathbb R^3}i\,w\Phi\,\mathcal N_H(Z)\,dx\\
&-4b\Re\int_{\mathbb R^3}w\Phi\,\Lambda Z\,dx\\
&+4\Re\int_{\mathbb R^3}w
    [\Phi-|V|^2\overline V]\,V_s\,dx .
\end{aligned} \tag{WF4}
\]
Here \(\partial_s w|_{R\ {\rm fixed}}=
 -(L'/L)(q/L)\chi'(q/L)K_R(q)\).
No second derivative of \(Z\) is present in WF4. The center boundary term vanishes by smooth radial regularity and the \(q^2\) measure; at \(q=L/3\) the cutoff vanishes. The Hartree term in WF4 is the *genuine* nonlocal nonlinearity and is not silently discarded; if \(V=0\), its real-phase pairing with \(\Phi\) cancels.

For the exact bound set
\[
\begin{gathered}
 B_U=\sup_{\Omega_L}(|V|+|Z|),\quad B_V=\sup_{\Omega_L}|V|,
 \quad e_0=\|Z\|_{L^2(\Omega_L)},\quad e_1=\|\nabla Z\|_{L^2(\Omega_L)},\\
 v_1=\|\nabla V\|_{L^2(\Omega_L)},\quad
 v_s=\|V_s\|_{L^2(\Omega_L)},\quad
 A_L=|\Omega_L|=\frac{4\pi L^3}{81},\quad
 J_\rho=\int_{\Omega_L}|\rho|\,dx .
\end{gathered}
\]
Since \(|\Phi|\le B_U^3\) and \(|\nabla\Phi|\le 3B_U^2(|\nabla V|+|\nabla Z|)\), WF3–WF4 imply
\[
\begin{aligned}
\left|\frac{d}{ds}Q_\chi(s,R(s))\right|
\le{}&
 \left(\frac{C_\chi|L'|}{3L}W_0+|R'|W_R\right)J_\rho\\
&+4W_1B_U^3A_L^{1/2}e_1
 +12W_0B_U^2(v_1+e_1)e_1\\
&+4W_0B_U^3\|\mathcal N_H(Z)\|_{L^1(\Omega_L)}\\
&+4|b|W_0B_U^3A_L^{1/2}
     \left(\frac{e_0}{2}+\frac L3e_1\right)\\
&+12W_0B_U^2e_0v_s.
\end{aligned} \tag{WF5}
\]
Also \(J_\rho\le4B_U^3 A_L^{1/2}e_0\). The final term in WF5 uses the **cubic difference**, \(|\Phi-|V|^2\overline V|\le3B_U^2|Z|\), so it vanishes when the physical radiation vanishes; a crude sum of the two cubic magnitudes would lose this cancellation. By the true 3D Hardy–Littlewood–Sobolev inequality, not a local-NLS replacement,
\[
 \|\mathcal N_H(Z)\|_{L^1(\Omega_L)}
 \le |\kappa_H|C_{\rm HLS}A_L^{1/6}\|Z\|_{L^6(\mathbb R^3)}^7. \tag{WF6}
\]
Indeed \(K*|Z|^4\in L^3\), \(|Z|^3\in L^{3/2}(\Omega_L)\), and finite-volume embedding \(L^6(\Omega_L)\hookrightarrow L^{9/2}(\Omega_L)\) supplies \(A_L^{1/6}\).

**Logical improvement over IM12:** WF5 requires \(\nabla Z\) and the genuine Hartree nonlinearity, but **not** the unbounded candidate \(P=\mathfrak M(\Delta z+\mathcal N_H(z))^{1/4}\), nor the absolute density velocity \(J_1=\int|\rho_s|\). This is a bound on the *derivative of the localized far-field potential*, not a pointwise bound on the density derivative. It uses only the original physical PDE and a valid weak integration-by-parts operation. The frozen reference \(V\) may move; its actual \(V_s\) remains explicitly present.

## 4. Source-faithful smooth-radiation scale corollary

For the very same physical Hartree solution \(z(t)\), suppose on the actual physical ball \(B_{\ell L/3}\) the genuine field norms
\[
 h_0=\|z(t)\|_{L^\infty(B_{\ell L/3})},\quad
 h_1=\|\nabla z(t)\|_{L^\infty(B_{\ell L/3})},\quad
 h_N=\|\mathcal N_H(z(t))\|_{L^\infty(B_{\ell L/3})}
\]
are finite; these are **actual orbit norms**, not hypothesized independent envelopes or temporal orders. The exact critical scaling yields
\[
 e_0\le\sqrt\ell\,h_0 A_L^{1/2},\qquad
 e_1\le\ell^{3/2}h_1 A_L^{1/2},\qquad
 \|\mathcal N_H(Z)\|_{L^1(\Omega_L)}
   \le\ell^{5/2}h_N A_L . \tag{WF7}
\]
Put \(\alpha=4\pi/81\), \(c_0=144/65\),
\(c_1=(256+432C_\chi)/195\),
\(c_R=384/65\), and \(B=B_U\). Substitution into WF5, with \(R'=\theta L'\), gives the **fully explicit parameter-smallness form**
\[
\begin{aligned}
\left|\frac d{ds}Q_\chi(s,\theta L)\right|
\le{}&
4\alpha B^3\sqrt\ell\,h_0 |L'|
   (c_0C_\chi/3+\theta c_R)
 +4c_1\alpha B^3\ell^{3/2}h_1\\
&+12c_0B^2\bigl(
 \sqrt\alpha\,\ell^{3/2}h_1L^{-1/2}v_1
 +\alpha\ell^3h_1^2L\bigr)
 +4c_0\alpha B^3\ell^{5/2}h_N L\\
&+4|b|c_0\alpha B^3
 (\tfrac12\sqrt\ell\,h_0L+\tfrac13\ell^{3/2}h_1L^2)
 +12c_0\sqrt\alpha\,B^2\sqrt\ell\,h_0L^{-1/2}v_s .
\end{aligned} \tag{WF8}
\]
Every term contains a genuine positive power of \(\ell\), with explicit geometric factors \(L,L',b\); in particular the main gradient-kernel term is \(O(\ell^{3/2}h_1)\) **independent of the matching radius \(L\)**. However **WF8 is not a positive power of renormalized time** unless the actual modulation PDE bounds \(\ell L\), \(b\), \(L'\), \(v_1\), \(v_s\), \(h_i\). It also does not estimate the outer near-diagonal Hartree source. WF8 does not assume a Type-II rate.

## 5. What the method still does *not* close

The bounded-energy norms on the right of WF5 have **not** been proved with a positive order in the renormalized time \(s\). For regular radiation, \(B_Z\le\sqrt\ell\,\|z(t)\|_\infty\), \(\nabla Z(x)=\ell^{3/2}\nabla z(t,\ell x)\), and \(\|\nabla Z\|_{L^2(\Omega_L)}=\|\nabla z\|_{L^2(B_{\ell L/3})}\), providing a genuine route to source smallness if the original regular flow and modulation geometry control \(\ell L\), but no such time rate is assumed here. Differentiated observer kernel \(\partial_RK\) is covered; the *moving Kummer basis*, unique two-speed derivative, full untruncated near-diagonal interaction, complete four-piece mismatch, \(C^1\) radial time trace, parameter Lipschitz, finite PDE recursion, and dynamically produced Type-II exponent remain open.

Related strictly accepted Lean inputs: ActualMomentPDEFlux.lean proves the original quartic Hartree phase cancellation; ActualHartreeFullInteractionTimeFromOrbit.lean proves the full fixed-observer three-potential chain rule under domination assumptions. **Neither file proves WF4–WF6**. The previously failed finite telescoping CI 42530158681 was repaired and strictly compiled in CI 42958494409 (job 130319187052), with only propext / Classical.choice / Quot.sound. The telescope is still a nonlinear identity, not a positive residual bound. No new Lean audit/CI is claimed for this note. **Original revised acceptance stays 11/13.**
