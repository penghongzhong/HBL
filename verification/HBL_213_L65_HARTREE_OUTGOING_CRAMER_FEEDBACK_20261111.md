# HBL §2.13 — true Hartree \(L^{6/5}\) feedback into the regular outgoing Cramer channel

**11 November 2026. Paper-level analytic estimate; NOT a new Lean theorem or a newly accepted original environment. Original count: 11/13.**

## 1. Retain the true original Green normalization

Let \(K\) be the existing origin-normalized Kummer pair with \(0<r_0<B<R\). Write
\[
X_K(r)=\operatorname{originPhysicalValue}(K.x,r)=K.x(r)/r,\qquad
Y_K(r)=K.y(r)/r,\qquad
W_K(r)=r^{-2}e^{-ir^2/4}.
\]
These are the *actual definitions and exact Wronskian* in
\`HBL/KummerOriginGreen/GreenBridge.lean\`; no substitute fundamental system is introduced.
For a radial source \(F(r)\), the original outgoing coefficient is
\[
\mathcal C_A^K[F]=\int_{r_0}^{B}{X_K(r)F(r)\over W_K(r)}\,dr
 =\int_{r_0}^{B} X_K(r)e^{ir^2/4}r^2F(r)\,dr. \tag{AC1}
\]
The existing regular-origin ODE estimate
\`origin_kummer_regular_physical_bound\` gives
\[
 |X_K(r)|\le C_X:=1+(D+1)GB^2,\quad 0<r\le B, \tag{AC2}
\]
under the actual coefficient and regularized-IVP budgets \(D,G\ge0\) appearing in that previously verified theorem. The radius \(r_0\) does not enter \(C_X\).

Identify \(F(r)\) with its radial extension \(F^\sharp(x)=F(|x|)\) on \(\mathbb R^3\). The *exact physical radial measure* is \(dx=4\pi r^2dr\). Hölder \(L^6\)-\(L^{6/5}\) yields
\[
\begin{aligned}
|\mathcal C_A^K[F]|
&\le {1\over4\pi}\,
 \|\mathbf1_{\{r_0<|x|<B\}} X_K(|x|)e^{i|x|^2/4}\|_{L^6_x}
 \,\|F^\sharp\|_{L^{6/5}_x}\\
&\le {C_X\over4\pi}\left({4\pi\over3}\right)^{1/6}
 B^{1/2}\|F^\sharp\|_{L^{6/5}_x}. \tag{AC3}
\end{aligned}
\]
This is an **exact no-left-radius-loss bound for the real original outgoing Cramer functional**, at a fixed Kummer configuration. Crucially the sharp endpoint indicator costs nothing in \(L^6\); no third spatial source jet or Morawetz-dual estimate is used.

## 2. The *full quartic nonlocal* feedback has precisely the needed Lebesgue integrability

Use the actual critical Hartree map
\[
\mathcal N_H(U)=\kappa_H(|x|^{-2}*|U|^4)|U|^2U .
\]
The explicit Hardy–Littlewood–Sobolev/Hölder proof already recorded in
\`verification/HBL_213_TRUE_HARTREE_C3_NONLOCAL_FEEDBACK_20261110.md\`, (NF1),
produces, for radial \(U,P\in\dot H^1(\mathbb R^3)\),
\[
\|\mathcal N_H(U+P)-\mathcal N_H(U)\|_{6/5}
 \le 7\kappa_H C_{\rm HLS}S^7
 (2\|\nabla U\|_2+\|\nabla P\|_2)^6\|\nabla P\|_2, \tag{AC4}
\]
where \(\|f\|_6\le S\|\nabla f\|_2\).
This is **stronger than just the earlier \(\dot H^{-1}\) estimate**;
it uses no independent pointwise nonlinearity envelope.

In the true Kummer coordinate the scaled source increment is
\(F_a(r)=a^2\{\mathcal N_H(U+P)-\mathcal N_H(U)\}(ar)\), \(a>0\).
The exact three-dimensional scaling gives
\[
\|F_a^\sharp\|_{6/5}
=a^{2-3/(6/5)}\|\mathcal N_H(U+P)-\mathcal N_H(U)\|_{6/5}
=a^{-1/2}\|\mathcal N_H(U+P)-\mathcal N_H(U)\|_{6/5}. \tag{AC5}
\]
Combining (AC3)–(AC5), without importing any positive time power,
\[
\boxed{\;
|\mathcal C_A^K[F_a]|
\le {7\kappa_HC_{\rm HLS}S^7 C_X\over4\pi}
       \left({4\pi\over3}\right)^{1/6}
       B^{1/2}a^{-1/2}
       (2\|\nabla U\|_2+\|\nabla P\|_2)^6
       \|\nabla P\|_2 .
\;} \tag{AC6}
\]
Consequently the **full seven-degree Hartree convolution feedback of an actual finite-energy splice can be inserted into the fixed regular outgoing Cramer channel without any hidden \(r_0^{-1}\) factor**. This applies to the source difference when \(U\to U+P\), not to arbitrary independent forcing. The given \(U,P\) must still be constructed from the genuine packet; (AC6) does not manufacture their time decay.

## 3. The singular Green channel has a genuinely different obstruction

The other exact Green integrand uses \(Y_K(r)=K.y(r)/r\):
\[
\mathcal C_B^K[F]=\int_{r_0}^B
          Y_K(r)e^{ir^2/4}r^2F(r)\,dr .
\]
Its \(L^{6/5}\)-dual kernel is \(Y_K(r)\mathbf1_{[r_0,B]}\).
Since the origin-normalized *actual* IVP satisfies \(K.y(0)=1\) and is continuous,
there exists fixed \(B_*>0\) such that
\(1/2\le |K.y(r)|\le2\) on \(0<r<B_*\). For \(0<r_0<B_*/2\), the
\(L^6(\mathbb R^3)\)-norm of this singular kernel is comparable to
\[
\left(4\pi\int_{r_0}^{B_*}r^{-4}\,dr\right)^{1/6}
 \asymp r_0^{-1/2}. \tag{AC7}
\]
By \(L^p\) duality, this loss is sharp **if only an arbitrary**
\(L^{6/5}\)-source bound is used (and radial maximizing sources suffice).
It does not prohibit source-specific moment cancellation or the
previously proved *complete* \(Y A_F\) singular-product estimate.

Thus (AC6) closes a specific regular-Cramer *nonlocal feedback norm*,
while the singular-channel moment/regularization, the moving Kummer
operator and endpoint, the selected-speed Jacobian changes, and the
full \(s^{-9/4}\) physical PDE residual remain separate tasks.
No independent envelope, positive time exponent or blowup rate has been assumed.

## 4. Acceptance and manuscript synchronization

This note is a complete **paper calculation**, not an audited Lean
declaration. The strict CI for the original Green/Wronskian producer and the
previously published HLS computation must not be mislabeled as a new strict
certificate for (AC1)–(AC7). It is a concrete route for the *nonlinear
outgoing Cramer response* in the original frozen configuration, **not**
original §2.13 closure, true finite packet recursion or a Type-II rate.
**Formal original acceptance remains exactly 11/13.**
