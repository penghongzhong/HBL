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


## 5. Eliminate ALL independently stated pointwise source envelopes using the **same correction** \(u\)

The preceding \(M,S,A\) are already defined from the actual
field; they can in fact all be **derived from just the two
physical radial correction norms \(U,H\)**, without taking
\(L^\infty\) or 3D density bounds as additional hypotheses.

For any radial complex \(u\in L^2(dr)\) that is locally
absolutely continuous with \(H=\|(1+r^2)u'\|_{L^2(dr)}<\infty\),
the weighted derivative is integrable at infinity:
\[
 \int_r^\infty|u'(t)|dt\le H
    \left(\int_r^\infty(1+t^2)^{-2}dt\right)^{1/2}.
\]
Thus \(u(\infty)\) exists, and \(u\in L^2(dr)\) forces
\(u(\infty)=0\). The fundamental theorem of calculus gives
\[
 \begin{aligned}
 |u(r)|
 &\le H\left(\int_r^\infty(1+t^2)^{-2}dt\right)^{1/2},\\
 \|u\|_{L^\infty(dr)}
 &\le\frac{\sqrt\pi}{2}H,\\
 \boxed{\qquad
 \sup_{r\ge0}\sqrt{1+r^2}|u(r)|
 &\le\sqrt{\frac\pi2}\,H .
 \qquad}
 \end{aligned}
 \tag{N13}
\]
The last line uses the **no-radius-loss** inequality
\[
 (1+r^2)\int_r^\infty(1+t^2)^{-2}dt
 \le\int_r^\infty(1+t^2)^{-1}dt\le\frac\pi2.
\]
Therefore, with no independent field or source envelope,
\[
 \boxed{
 |W(r)+u(r)|\le K\,W(r),\qquad
 K:=1+\sqrt{\frac\pi2}\,H ,
 }\tag{N14}
\]
so \(M\le K\), \(S\le K^3\) in (N1).

The actual quartic density difference enjoys the **extra
bubble weight**
\[
 |\rho(r)|=\big||W+u|^4-W^4\big|
 \le4K^3W(r)^3|u(r)|.
\tag{N15}
\]
For the true 3D Riesz potential, this gives directly
\[
 \begin{aligned}
 \|\rho\|_\infty
 &\le2\sqrt\pi K^3H,\\
 \|\rho\|_{L^1(\mathbb R^3)}
 &\le16\pi K^3
    \left(\int_0^\infty\frac{r^4}{(1+r^2)^3}dr\right)^{1/2}
    U\\
 &=4\pi\sqrt{3\pi}\,K^3 U,
 \qquad
 \int_0^\infty\frac{r^4}{(1+r^2)^3}dr=\frac{3\pi}{16}.
 \end{aligned}
 \tag{N16}
\]
Consequently the exact deterministic \(A\) from (N1)
has the **fully reduced original-field budget**
\[
 \boxed{\qquad
 A\le A_\ast(U,H):=
 \frac{12}{\pi}K^3\bigl(
     2\sqrt\pi\,H+\sqrt{3\pi}\,U\bigr),
 \qquad K=1+\sqrt{\frac\pi2}\,H .
 \qquad}
 \tag{N17}
\]
There is no separately assumed \(\|V\|_\infty\),
\(\|\rho\|_{L^1}\), \(\|\rho\|_\infty\), nor
nonlocal Riesz-gradient source bound.

Substitution in the original full quartic (N11)--(N12)
produces the completely explicit source-faithful nonlinear map
\[
 \boxed{\begin{aligned}
 &\|(1+r^2)\partial_r[
       \mathcal N_{\rm H}(W+u)-\mathcal N_{\rm H}(W)]
       \|_{L^2(dr)}\\
 &\quad\le
 (24C_{\rm A2}K^6+9K^2+18K)\,U+9K^2H
 +A_\ast(U,H)
  \bigl(3\sqrt\pi/4+3K^2H+6KU\bigr),\\[2pt]
 &\|\mathcal N_{\rm H}(W+u)-\mathcal N_{\rm H}(W)\|_{L^2(dr)}
 \le A_\ast(U,H)K^2(\sqrt{\pi/2}+U)+9K^2U .
 \end{aligned}}\tag{N18}
\]
This is **not** a schematic or assumed small-source
statement: each coefficient is an explicit expression
in the actual \(U=\|u\|_{L^2(dr)}\),
\(H=\|(1+r^2)u'\|_{L^2(dr)}\) and the universal
published fixed-weight Riesz constant \(C_{\rm A2}\).

As \(U+H\to0\), \(K\to1\) and the right-hand side
is \(O(U+H)\). This is a genuine nonlinear local
continuity result in a radial weighted Sobolev topology,
**not** a proof that the full time-moving selected
four-region correction satisfies \(U(s)+H(s)=O(s^{-\nu})\).
That latter estimate must come from the original
Fredholm/Kummer PDE and true physical modulation law.
The full spatial residual also retains local Laplacian,
moving-cutoff transport, spectral and parameter derivative
terms; the homogeneous-adjoint Hartree Kato inverse,
actual orbit and dynamically selected blowup rate
remain unproved. No additional Lean axiom or original
13-environment acceptance is introduced.
