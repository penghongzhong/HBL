# Full physical Hartree quadratic remainder without a shell-volume factor

**10 November 2026. Paper proof only. Original revised count 11/13.** This is a functional estimate for the *complete original nonlinearity*, not a certificate of the full four-region PDE residual or a constructed orbit. It gives an alternative energy-source estimate for the same actual assembled field; it does not replace any Fredholm source norm without a separate interface proof.

## 1. A physical norm and an elementary potential estimate

All norms in this note are on three-dimensional Lebesgue measure, not radial dr. Set
\[
 X=\dot H^1(\mathbb R^3)\cap L^6(\mathbb R^3)\cap L^\infty(\mathbb R^3),
 \qquad \|v\|_X=\|\nabla v\|_2+\|v\|_6+\|v\|_\infty.
\]
For the original normalized potential
\(\mathcal I\rho=(3/\pi^2)|x|^{-2}*\rho\), split the actual kernel at unit distance. Since
\[
 \||x|^{-2}\mathbf1_{|x|\le1}\|_1=4\pi,\qquad
 \||x|^{-2}\mathbf1_{|x|>1}\|_3=(4\pi/3)^{1/3},
\]
Holder's inequality gives
\[
 \|\mathcal I(f_1f_2f_3f_4)\|_\infty
 \le\frac3{\pi^2}\left(4\pi\prod_{j=1}^4\|f_j\|_\infty
 +(4\pi/3)^{1/3}\prod_{j=1}^4\|f_j\|_6\right)
 \le C_0\prod_{j=1}^4\|f_j\|_X,
\tag{E1}
\]
where \(C_0=(3/\pi^2)[4\pi+(4\pi/3)^{1/3}]\).
Complex conjugation of any factor changes none of these bounds.

There is a simpler **unweighted physical derivative** than the weighted radial A2 route: in the convention \(\widehat f(\xi)=\int e^{-ix\cdot\xi}f(x)dx\),
\[
 \widehat{\mathcal I\rho}=6|\xi|^{-1}\widehat\rho,
 \quad
 \widehat{\nabla\mathcal I\rho}=6i\xi|\xi|^{-1}\widehat\rho,
 \quad
 \|\nabla\mathcal I\rho\|_{L^2(\mathbb R^3)}=6\|\rho\|_2.
\tag{E2}
\]
The last identity is exactly Plancherel with the vector norm; it is not an assumed Hartree smoothing estimate. In particular, interpolation
\(\|f\|_8\le\|f\|_6^{3/4}\|f\|_\infty^{1/4}\le\|f\|_X\)
implies
\[
 \|\nabla\mathcal I(f_1f_2f_3f_4)\|_2
 \le6\prod_{j=1}^4\|f_j\|_X.
\tag{E3}
\]
No derivative of the quartic density, shell radius or cutoff width occurs in (E3).

## 2. The actual seven-linear Hartree map

Define the real-multilinear map
\[
 T(f_1,\ldots,f_7)
 =\mathcal I(f_1f_2\overline{f_3}\overline{f_4})
       f_5f_6\overline{f_7}.
\]
Then \(\mathcal N(u)=T(u,\ldots,u)\) is exactly
\(\mathcal I(|u|^4)|u|^2u\), not a local surrogate.
The distributional product rule, (E1) and (E3) give
\[
 \boxed{\quad
 \|\nabla T(f_1,\ldots,f_7)\|_2
 \le C_T\prod_{j=1}^7\|f_j\|_X,
 \qquad C_T=6+3C_0.
 \quad}\tag{E4}
\]
The first term differentiates the genuine nonlocal potential and uses all three exterior factors in L-infinity; the other three terms differentiate one exterior factor in L2 and use (E1). Thus every nonlocal density interaction is retained. Also
\(\|T\|_6+\|T\|_\infty\le2C_0\prod_j\|f_j\|_X\),
so this is a continuous real polynomial X to X, with X-operator constant at most \(6+5C_0\).

These statements hold first for smooth profiles. For the displayed X-class, the density belongs to both L2 and L3/2, the potential is bounded by (E1), its weak gradient is (E2), and local Sobolev product rules prove the same conclusions directly. Thus no unproved density of compact functions in the L-infinity norm is required.

## 3. A quadratic remainder of the entire assembled PDE nonlinearity

For the *actual* global background U and actual correction H, define
\[
 R_U(H)=\mathcal N(U+H)-\mathcal N(U)-D\mathcal N(U)[H],
\]
where D is the real derivative (so all conjugate terms are included).
The exact seven-linear expansion and Taylor's integral identity give
\[
 \boxed{\quad
 \|R_U(H)\|_{\dot H^1}
 \le21C_T(\|U\|_X+\|H\|_X)^5\|H\|_X^2.
 \quad}\tag{E5}
\]
Indeed the second derivative has 7 times 6 terms, each bounded by (E4), and the Taylor weight integrates to one half. This is a proof of the nonlinear quadratic bound, not a postulated residual estimate.

For a fixed physical background U, the exact derivative
\(DR_U(H)=D\mathcal N(U+H)-D\mathcal N(U)\)
yields the same-source two-correction Lipschitz bound
\[
 \|R_U(H)-R_U(K)\|_{\dot H^1}
 \le42C_T(\|U\|_X+\|H\|_X+\|K\|_X)^5
       (\|H\|_X+\|K\|_X)\|H-K\|_X.
\tag{E6}
\]
For changing actual backgrounds, an additional explicit term suffices:
\[
 \|R_U(K)-R_V(K)\|_{\dot H^1}
 \le105C_T(\|U\|_X+\|V\|_X+\|K\|_X)^4
          \|K\|_X^2\|U-V\|_X.
\tag{E7}
\]
The coefficient 105 is \(7\cdot6\cdot5/2\), from the third derivative and the same Taylor weight. Applying (E6) and (E7) together gives a full background-and-correction estimate, rather than silently fixing the nonlinear PDE background while varying its parameters.

## 4. The physical radiation scaling is uniform in this norm

For the SAME critical radiation
\(Z_\ell(x)=\sqrt\ell\,z(\ell x)\), \(0<\ell\le1\),
\[
 \|Z_\ell\|_6=\|z\|_6,\qquad
 \|\nabla Z_\ell\|_2=\|\nabla z\|_2,\qquad
 \|Z_\ell\|_\infty=\sqrt\ell\,\|z\|_\infty.
\tag{E8}
\]
Hence the true background W+Z_ell is bounded in X whenever the physical radiation is bounded in X, with no inverse-ell loss. This is not the stronger weighted-radial norm used in the earlier Kato-dual analysis; the two norms must not be identified.

## 5. Exact consequence and strict limitation for the time budget

**Conditional consequence, not an established physical input:** if the *actual assembled four-region correction* obeys
\(\|H(s)\|_X\le C_Hs^{-9/8}\), while \(\|U(s)\|_X\le M\), then for s at least 1, (E5) gives
\[
 \|R_{U(s)}(H(s))\|_{\dot H^1}
 \le21C_T(M+C_H)^5C_H^2s^{-9/4}.
\tag{E9}
\]
In this physical energy norm the *nonlinear Taylor remainder alone* has no shell-volume multiplier \(s^{3/8}\). If, separately, an appropriate projected physical energy propagator is uniformly bounded with constant C_U, its absolute Duhamel contribution is at most
\[
 \frac45 C_U\,21C_T(M+C_H)^5C_H^2s^{-5/4},
\tag{E10}
\]
which is smaller than the correction scale \(s^{-9/8}\) by \(s^{-1/8}\). Thus the earlier \(s^{1/4}\) loss is not an intrinsic loss of the full Hartree nonlinear map in every physical norm.

**Not proved here:** the actual H has the assumed X-bound; the full moving linear/principal/cutoff residual has order 9/4 in physical energy; the genuine projected propagator has the uniform bound C_U; or the fixed point preserves the extra L-infinity control. In particular the existing normalized Kummer H1 certificate acquires a factor a in physical energy after y=a*r. This factor must be paid by the real source, not deleted. The static Fredholm forcing still needs its own weighted norms; (E9) cannot be substituted into that interface without proof.

This calculation is a useful *full-map source estimate*, not a new Hartree spectral theorem. It avoids imposing an unnecessary Kato theorem on this one nonlinear term, but does not remove the need for an actual physical linear inverse, same-orbit norm estimates, or dynamic modulation closure. It introduces no Lean axiom. **No new original environment accepted: 11/13.**
