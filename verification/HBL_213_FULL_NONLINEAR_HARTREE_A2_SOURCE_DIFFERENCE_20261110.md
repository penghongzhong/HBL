# HBL §2.13: a global, original-quartic Hartree source-gradient estimate from true fields

**Date:** 10 November 2026. **Status:** Complete paper-level functional inequality, using the published weighted \(A_2\) Riesz-transform theorem; not yet Lean formalized. It is neither an imposed positive-time-order hypothesis nor an independent source envelope. **Original 13-environment acceptance stays 11/13.**

## 1. Setup from the original 3D energy-critical Hartree equation

Let
\[
 W(r)=(1+r^2)^{-1/2},\quad \kappa_{\rm H}=3/\pi^2,\quad
 \mathcal If=\kappa_{\rm H}(|x|^{-2}*f),
\]
\[
 \mathcal N_{\rm H}(V)
  =\mathcal I(|V|^4)\,|V|^2V .
\]
Here \(V=W+u\) is any sufficiently smooth **actual radial complex
physical field** with all displayed norms finite; later the desired
\(u\) is the literal same-orbit four-piece correction, not an abstract
independent source. Put
\[
 \rho=|V|^4-W^4,\quad
 \Delta P=\mathcal I\rho,\quad
 P_W=\mathcal I(W^4)=3W^2,\quad
 Q(z)=|z|^2z ,
\]
and define *from \(V,u\) themselves*
\[
 \begin{gathered}
 M=\max(1,\|V\|_{L^\infty(dr)}),\qquad
 S=\|(1+r^2)|V|^3\|_{L^\infty(dr)},\\
 U=\|u\|_{L^2(dr)},\qquad
 H=\|(1+r^2)u'\|_{L^2(dr)},\\
 A=\kappa_{\rm H}\left(
      4\pi\|\rho\|_{L^\infty(\mathbb R^3)}
      +\|\rho\|_{L^1(\mathbb R^3)}
   \right).
 \end{gathered}
 \tag{N1}
\]
All norms are **explicit functionals of the same genuine field**;
no decay, Lipschitz or blowup-rate bound is assumed for them.

The elementary near-/far-kernel splitting gives **for every** \(x\),
\[
 |\Delta P(x)|
 \le\kappa_{\rm H}\int_{|x-y|<1}|x-y|^{-2}|\rho(y)|dy
    +\kappa_{\rm H}\int_{|x-y|\ge1}|\rho(y)|dy
 \le A ,
 \tag{N2}
\]
since \(\int_{|z|<1}|z|^{-2}dz=4\pi\).
For radial fields, the global weighted \(A_2\) Riesz theorem
proved/applicable in
\`HBL_213_GLOBAL_RIESZ_A2_NO_INNER_RADIUS_LOSS_20261110.md\`
gives, with a **fixed** finite \(C_{\rm A2}\),
\[
 \|\partial_r\Delta P\|_{L^2(dr)}
 \le6C_{\rm A2}\|\rho\|_{L^2(dr)}
 \le24C_{\rm A2}M^3U .
 \tag{N3}
\]
The final inequality is pointwise:
\[
 \big||V|^4-W^4\big|
 \le4M^3|V-W|=4M^3|u|.
 \tag{N4}
\]
There is no \(R^{-1}\) term at the physical origin, and
nothing resembling an independent Riesz-gradient envelope.

## 2. Exact complex cubic differential and Lipschitz identity

For \(z,h\in\mathbb C\), the real Fréchet derivative is
\[
 DQ(z)h=|z|^2h+2\operatorname{Re}(\bar zh)\,z.
\]
Consequently, whenever \(|z|,|w|\le M\),
\[
 |DQ(z)h|\le3M^2|h|,\qquad
 |(DQ(z)-DQ(w))h|\le6M|z-w||h|.
 \tag{N5}
\]
Therefore for differentiable radial \(V=W+u\),
\[
 \begin{aligned}
 |Q(V)-Q(W)|&\le3M^2|u|,\\
 |(Q(V)-Q(W))'|
 &\le3M^2|u'|+6M|u||W'|.
 \end{aligned}
 \tag{N6}
\]
The original real bubble has
\[
 \begin{gathered}
 \|P_W\|_\infty=3,\qquad
 \|(1+r^2)P_W'\|_\infty
 =\sup_{r>0}\frac{6r}{1+r^2}=3,\\
 \|(1+r^2)W'\|_\infty\le1,\qquad
 \|(1+r^2)(W^3)'\|_{L^2(dr)}
 =3\biggl(\int_0^\infty
        \frac{r^2}{(1+r^2)^3}dr\biggr)^{1/2}
 =\frac{3\sqrt\pi}{4}.
 \end{gathered}
 \tag{N7}
\]
It follows exactly that
\[
 \|(1+r^2)(Q(V)-Q(W))'\|_2
 \le3M^2H+6MU .
 \tag{N8}
\]

## 3. Full original nonlocal Hartree cubic-quartic difference

The correct **nonlinear** decomposition is
\[
 \mathcal N_{\rm H}(V)-\mathcal N_{\rm H}(W)
 =\Delta P\,Q(V)+P_W[Q(V)-Q(W)]
 \tag{N9}
\]
and, after the product rule,
\[
 \begin{aligned}
 [\mathcal N_{\rm H}(V)-\mathcal N_{\rm H}(W)]'
 ={}&
 (\Delta P)'Q(V)
 +P_W'[Q(V)-Q(W)]\\
 &+\Delta P\,[Q(W)'+(Q(V)-Q(W))']\\
 &+P_W(Q(V)-Q(W))'.
 \end{aligned}
 \tag{N10}
\]
Equations (N2)--(N8) now give, **globally on the radial half-line**,
\[
 \boxed{\begin{aligned}
 \|(1+r^2)\partial_r[
   \mathcal N_{\rm H}(W+u)-\mathcal N_{\rm H}(W)]
   \|_{L^2(dr)}
 \le{}&
  (24C_{\rm A2}SM^3+9M^2+18M)U
  +9M^2 H\\
 &+A\left(\frac{3\sqrt\pi}{4}
          +3M^2H+6MU\right).
 \end{aligned}}
 \tag{N11}
\]
Indeed, (N10)'s four terms are bounded respectively by
\(24C_{\rm A2}SM^3U\), \(9M^2U\),
\(A(3\sqrt\pi/4+3M^2H+6MU)\),
and \(9M^2H+18MU\).

The undifferentiated source satisfies, as another explicit corollary,
\[
 \boxed{\quad
 \|\mathcal N_{\rm H}(W+u)-\mathcal N_{\rm H}(W)\|_{L^2(dr)}
 \le A M^2\left(\sqrt{\frac\pi2}+U\right)+9M^2U .
 \quad}\tag{N12}
\]
This uses \(\|W\|_{L^2(dr)}=\sqrt{\pi/2}\) and
\(|Q(V)|\le M^2|V|\).
No derivative of \(W\) with nonintegrable \((1+r^2)\) weight
is ever estimated separately: the difference decomposition
(N9)--(N10) **retains the actual bubble cancellations**.

## 4. Precise §2.13 scope

Unlike the earlier global \(L_+\) Hessian bound, (N11)–(N12)
control the **complete original quartic Hartree nonlinearity
minus its true stationary bubble contribution**, including
the density difference and its true nonlocal convolution.
They require only measurable, explicitly displayed
norms of the actual same-orbit \(u\), not an independently
assumed \(\mathcal I\)-gradient envelope.

**Still OPEN:** show the already constructed true source-selected
Fredholm/Kummer **moving four-piece field** has
\(M(s),S(s),U(s),H(s),A(s)\) of sufficiently small
PDE-derived size on the actual scales, with uniform
parameter Lipschitz and moving-interface time derivatives.
Then combine (N11) with the complete local Laplacian,
modulation, transport, spectral and external-shell residual;
one also needs the projected coupled Hartree Hamiltonian
homogeneous-adjoint Kato/physical inverse to construct the
genuine orbit and derive the rate dynamically.

Thus this is a *finished analytic norm inequality for the true
nonlocal source*, **not** the original \(\S2.13\) assertion of
positive time gain and not yet any new three-axiom Lean CI.
Neither \(12/13\) nor \(13/13\) is claimed.
