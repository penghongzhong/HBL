# HBL §2.13 — untruncated near-diagonal Hartree potential velocity via a Calderón–Zygmund flux

12 November 2026 (UTC). **New paper-level lemma, not Lean verified.** The revised original acceptance remains **11/13**. This extends the separated-observer weak-flux identity in \`HBL_213_REMOTE_HARTREE_WEAK_PDE_FLUX_20261111.md\` to the **entire** three-dimensional inverse-square convolution, including the near-diagonal region. It does not claim a full four-piece nonlinear residual or a positive time gain.

## 1. Exact original PDE and distributional continuity identity

Fix the genuine three-dimensional energy-critical Hartree equation
\[
 iz_t+\Delta z+\mathcal N_H(z)=0,\qquad
 \mathcal N_H(z)=\kappa_H(|x|^{-2}*|z|^4)|z|^2z,
 \quad\kappa_H\in\mathbb R .
\]
Let \(\ell_s=-b\ell,\ t_s=\ell^2\) and \(Z(s,x)=\sqrt{\ell(s)}z(t(s),\ell(s)x)\). For a real or complex *actual moving reference field* \(V(s,x)\), put \(U=V+Z\). At fixed \(x\),
\[
 Z_s=i(\Delta Z+\mathcal N_H(Z))-b\Lambda Z,\qquad
 \Lambda Z=\tfrac12Z+x\cdot\nabla Z. \tag{ND1}
\]
Set \(K(x)=|x|^{-2}\), \(\rho=|U|^4-|V|^4\), \(\Phi(q)=|q|^2\overline q\), and \(Q=K*\rho\).
For smooth rapidly decreasing fields (or, by density, fields for which the displayed products and distributional limits are defined),
\[
 \rho_s=\operatorname{div}J+R, \tag{ND2}
\]
where the **real** vector flux and source are
\[
\begin{aligned}
 J&=4\operatorname{Re}\big(i\Phi(U)\nabla Z\big),\\
 R&=-4\operatorname{Re}\big(i\nabla\Phi(U)\cdot\nabla Z\big)
  +4\operatorname{Re}\big(i\Phi(U)\mathcal N_H(Z)\big)\\
  &\quad-4b\operatorname{Re}\big(\Phi(U)\Lambda Z\big)
  +4\operatorname{Re}\big((\Phi(U)-\Phi(V))V_s\big).
\end{aligned}\tag{ND3}
\]
Proof: \(\partial_s|q|^4=4\operatorname{Re}(\Phi(q)q_s)\); insert (ND1) and expand \(\operatorname{div}(\Phi(U)\nabla Z)\). All terms involving \(V_s\) combine into the *difference* \(\Phi(U)-\Phi(V)\). No assumption that the assembled \(U\) solves the same PDE is made.

Thus, without any radial cutoff or exclusion of \(x=y\),
\[
 \boxed{\quad Q_s=\sum_{j=1}^3(\partial_j K)*J_j+K*R\quad}
 \qquad\text{in distributions}. \tag{ND4}
\]
The gradient kernel must be interpreted as a **principal-value distribution**. Estimating \(|\nabla K|=2|x|^{-3}\) by absolute convolution would diverge at \(x=y\), and is NOT a valid proof.

## 2. Untruncated strong \(L^2\) estimate with one radiation derivative

For the Fourier convention \(\widehat f(\xi)=\int e^{-ix\cdot\xi}f(x)\,dx\),
\[
 \widehat K(\xi)=2\pi^2|\xi|^{-1},\qquad
 \widehat{(\partial_jK)*J_j}
   =2\pi^2 i\frac{\xi_j}{|\xi|}\widehat{J_j}.
\]
Plancherel, summed as a **vector** multiplier (not a sum of three separate operator norms), implies
\[
 \left\|\sum_j(\partial_jK)*J_j\right\|_2
 \le 2\pi^2\|J\|_2. \tag{ND5}
\]
The genuine Riesz-potential HLS bound \(K:L^{6/5}\to L^2\) gives
\[
 \boxed{\|Q_s\|_2\le2\pi^2\|J\|_2+C_{6/5\to2}^{\rm HLS}\|R\|_{6/5}.} \tag{ND6}
\]
This is global and includes the **near-diagonal** nonlocal interaction. It does not contain \(\Delta Z\) or the separated-observer derivative \(J_1=\int|\rho_s|\).

For a transparent sufficient source-faithful criterion, suppose the actual fields at the selected time satisfy
\[
 M=\max(\|U\|_\infty,\|V\|_\infty)<\infty,\qquad
 \nabla Z\in L^2,\quad\nabla U\in L^3,\quad
 \mathcal N_H(Z)\in L^{6/5},
\]
and the **actual products** \(\Phi(U)\Lambda Z\) and
\((\Phi(U)-\Phi(V))V_s\) belong to \(L^{6/5}\).
Using \(|\nabla\Phi(U)|\le3|U|^2|\nabla U|\), Hölder, and \(|\Phi(U)-\Phi(V)|\le3M^2|Z|\), (ND6) yields
\[
\begin{aligned}
\boxed{\ 
\|Q_s\|_{L^2(\mathbb R^3)}
\le{}&8\pi^2M^3\|\nabla Z\|_2\\
&+C_{6/5\to2}^{\rm HLS}\Big(
 12M^2\|\nabla U\|_3\|\nabla Z\|_2
 +4M^3\|\mathcal N_H(Z)\|_{6/5}\\
&\hspace{35mm}
 +4|b|\|\Phi(U)\Lambda Z\|_{6/5}
 +4\|(\Phi(U)-\Phi(V))V_s\|_{6/5}\Big).
\end{aligned}} \tag{ND7}
\]
All inputs are norms of the **same actual physical orbit and selected packet**. Their finiteness is a condition for applying this estimate, not a manufactured decay rate. In particular \(\mathcal N_H(Z)\) is the original seven-linear *nonlocal* term.

## 3. Critical-scale obstruction to inferring a temporal gain

The same exact rescaling shows
\[
 \nabla Z_\ell(x)=\ell^{3/2}\nabla z(t,\ell x),\qquad
 \boxed{\|\nabla Z_\ell\|_{L^2(\mathbb R^3)}
       =\|\nabla z(t)\|_{L^2(\mathbb R^3)}.}\tag{ND8}
\]
Therefore (ND7), despite removing both the second spatial derivative and the nonintegrable near-diagonal absolute kernel, **cannot by itself produce a positive power of \(\ell\)** in its first term: the global radiation energy is scaling-invariant. If \(z\not\equiv0\) has nonzero \(\dot H^1\) energy, then no bound \(\|\nabla Z_\ell\|_2\le C\ell^\gamma\) with fixed \(C,\gamma>0\) can follow from critical rescaling alone.

This is a precise obstruction to promoting the full untruncated potential-velocity bound to the original \(s^{-9/4}\) physical residual estimate by a mere small-\(\ell\) argument. To obtain an actual gain one must **either** use a localized shrinking physical region and control its energy together with the complementary remote quartic density, **or** prove a cancellation induced by the same selected modulation equations. The localized energy identity is exact:
\[
 \|\nabla Z_\ell\|_{L^2(B_R)}=
 \|\nabla z(t)\|_{L^2(B_{\ell R})}. \tag{ND9}
\]
For fixed \(t\) and \(\ell R\to0\), the right side tends to zero by absolute continuity of the integral; **no uniform temporal power** follows unless regularity, geometry and evolution norms are quantitatively controlled.

## 4. Strict acceptance boundary

The locked jobs [43135036481](https://github.com/penghongzhong/HBL/actions/runs/43135036481) and [43124289518](https://github.com/penghongzhong/HBL/actions/runs/43124289518) certify, respectively, the selected fixed-time three \(C^1\) spatial joins/quadratic spectral correction and the exact nonlinear four-piece PDE telescope (only \`propext\`, \`Classical.choice\`, \`Quot.sound\`). Neither checks ND1–ND9, and an algebraic telescope is not a residual-gain theorem.

Next valid original-paper gate: establish *quantitative localized* energy/radiation and remote-density differences for the same selected physical profile, obtain the moving Kummer/real-selector derivatives, and close the complete four-region residual in the paper's exact target norm with positive time order and parameter Lipschitz. Actual finite recursion and the dynamically determined Type-II rate remain open. **Original revised theorem environments: 11/13.**
