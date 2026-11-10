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


## 6. The entire **nonlinear** source estimate is exact at every moving bubble scale

This is a useful difference from applying a fixed-bubble result at a
wrong physical radius. For arbitrary \(\lambda>0\), let
\[
 W_\lambda(r)=\lambda^{-1/2}W(r/\lambda),\quad
 u_\lambda(r)=\lambda^{-1/2}u(r/\lambda),\quad
 V_\lambda=W_\lambda+u_\lambda .
\]
Because the **original** cubic-quartic Riesz nonlinearity is
energy-critical in \(3D\),
\[
 \boxed{\quad
 \mathcal N_{\rm H}(V_\lambda)(\lambda \rho)
   =\lambda^{-5/2}\mathcal N_{\rm H}(W+u)(\rho).
 \quad}\tag{N19}
\]
Indeed, the complete convolution obeys
\[
 \mathcal I(|V_\lambda|^4)(\lambda\rho)
 =\lambda^{-1}\mathcal I(|W+u|^4)(\rho)
\]
(the volume/kernel/density factors are
\(\lambda^3\lambda^{-2}\lambda^{-2}\)), while the
complex cubic multiplier \(Q(V_\lambda)\) contributes
\(\lambda^{-3/2}\).
No local-NLS approximation or independent nonlocal
source term has been substituted.

Define the **true physical** norms
\[
 U_\lambda=\|u_\lambda\|_{L^2(dr)},\qquad
 H_\lambda=\|(\lambda^2+r^2)\partial_r u_\lambda\|_{L^2(dr)}.
\]
The exact change of variables gives
\[
 U_\lambda=U,\quad H_\lambda=\lambda H,
 \tag{N20}
\]
and, by differentiating (N19),
\[
 \begin{aligned}
 &\|\mathcal N_{\rm H}(V_\lambda)
   -\mathcal N_{\rm H}(W_\lambda)\|_{L^2(dr)}
   =\lambda^{-2}
    \|\mathcal N_{\rm H}(W+u)-\mathcal N_{\rm H}(W)\|_{L^2(d\rho)},\\
 &\|(\lambda^2+r^2)\partial_r[
   \mathcal N_{\rm H}(V_\lambda)
   -\mathcal N_{\rm H}(W_\lambda)]\|_{L^2(dr)}
   =\lambda^{-1}
    \|(1+\rho^2)\partial_\rho[
      \mathcal N_{\rm H}(W+u)
      -\mathcal N_{\rm H}(W)]\|_{L^2(d\rho)} .
 \end{aligned}\tag{N21}
\]
Introduce \(h=H_\lambda/\lambda\),
\(k=1+\sqrt{\pi/2}\,h\), and
\(a_*=(12/\pi)k^3(2\sqrt\pi\,h+\sqrt{3\pi}\,U_\lambda)\).
In the same exact physical norm as (N21), the
fully derived original nonlinear Hartree estimate is
\[
 \boxed{\begin{aligned}
 \|\mathcal N_{\rm H}(V_\lambda)
   -\mathcal N_{\rm H}(W_\lambda)\|_{L^2(dr)}
 &\le\lambda^{-2}\left[
 a_* k^2(\sqrt{\pi/2}+U_\lambda)
 +9k^2U_\lambda\right],\\
 \|(\lambda^2+r^2)\partial_r[
   \mathcal N_{\rm H}(V_\lambda)
   -\mathcal N_{\rm H}(W_\lambda)]\|_{L^2(dr)}
 &\le\lambda^{-1}\Big[
 (24C_{\rm A2}k^6+9k^2+18k)U_\lambda+9k^2h\\
 &\hspace{1.9cm}+
 a_*(3\sqrt\pi/4+3k^2h+6kU_\lambda)\Big].
 \end{aligned}}\tag{N22}
\]
This holds for **every** positive \(\lambda\), with
no independently postulated \(u\)-envelope, derivative
source norm, modulation path, or blowup rate. Conversely,
for an arbitrary true moving correction
\(u_{\rm phys}(s,r)\), define the normalized
\(u(s,\rho)=\sqrt{\lambda(s)}
u_{\rm phys}(s,\lambda(s)\rho)\);
(N22) then applies at each \(s\) **if** its physical
two norms are finite, without presupposing how the PDE
selects \(\lambda(s)\).

The estimate precisely fixes the scale factors
\(\lambda^{-2}\) and \(\lambda^{-1}\) that must enter
the **actual PDE source budget**. They are neither
positive-time gains nor proof of a nonlinear orbit:
the original modulation law and physical residual
must control \(U_\lambda(s)\), \(H_\lambda(s)\), and
their parameter/time derivatives in the correct
spaces. The full moving-cutoff Laplacian and the
real-Hartree linearized matrix resolvent remain
separately unclosed. Original **11/13** unchanged;
this is paper analysis, not a new Lean CI or axiom.


## 7. GENUINE two-field nonlinear Lipschitz bound in the SAME weighted source space

The full nonlinear source must be Lipschitz under the genuine
moving parameter dependence of the physical field. This
requires a **difference inequality**, not merely (N18)
at one field.

Let the two actual complex radial corrections be \(u,v\)
with \(U_u=\|u\|_2\), \(H_u=\|(1+r^2)u'\|_2\),
\(U_v,H_v\) similarly. Set
\[
 D=\|u-v\|_2,\quad
 J=\|(1+r^2)(u'-v')\|_2,\quad
 K=1+\sqrt{\pi/2}\max(H_u,H_v).
 \tag{N23}
\]
As established by the same weighted FTC in (N13),
\[
 |W+u|,|W+v|\le K W,\quad
 \|u-v\|_\infty\le\frac{\sqrt\pi}{2}J.
 \tag{N24}
\]
For any pair of profiles \(a,b\), define
\[
 A_{ab}:=\frac{12}{\pi}K^3
   \bigl(2\sqrt\pi\,H_{a-b}
            +\sqrt{3\pi}\,U_{a-b}\bigr).
\]
In particular let \(A_{uv}\) use \(D,J\),
and let \(A_v\) denote the right side with \(U_v,H_v\).
The exact original quartic density differences satisfy
\[
 \begin{aligned}
 &\|\mathcal I(|W+u|^4-|W+v|^4)\|_\infty\le A_{uv},\\
 &\|\partial_r\mathcal I(|W+u|^4-|W+v|^4)\|_{L^2(dr)}
     \le24C_{\rm A2}K^3D,\\
 &\|\mathcal I(|W+v|^4-W^4)\|_\infty\le A_v,\\
 &\|\partial_r\mathcal I(|W+v|^4-W^4)\|_{L^2(dr)}
     \le24C_{\rm A2}K^3U_v.
 \end{aligned}\tag{N25}
\]
Each \(A\) is a derived explicit polynomial in the
true same-field correction norms, **not** a separate
assumed bound.

Write \(X=W+u\), \(Y=W+v\),
\(P_Z=\mathcal I(|Z|^4)\), \(Q(Z)=|Z|^2Z\).
The original nonlinear difference decomposition is
\[
 \boxed{\quad
 \mathcal N_{\rm H}(X)-\mathcal N_{\rm H}(Y)
   =[P_X-P_Y]Q(X)+P_Y[Q(X)-Q(Y)] .
 \quad}\tag{N26}
\]
Both absolute and differentiated difference estimates
follow from the real Fréchet derivative
\(DQ(z)h=|z|^2h+2\operatorname{Re}(\bar zh)z\):
\[
 \begin{aligned}
 |Q(X)-Q(Y)|&\le3K^2W^2|u-v|,\\
 |(Q(X)-Q(Y))'|
 &\le3K^2W^2|u'-v'|
      +6KW|u-v|\,|W'+v'|.
 \end{aligned}\tag{N27}
\]
The **critical weighted radial** identities are
\[
 \|(1+r^2)W^2\|_\infty=1,\quad
 \|(1+r^2)WW'\|_2=\frac{\sqrt\pi}{2},\quad
 \|W'\|_2=\frac{\sqrt\pi}{4}.
\]
From (N24)–(N27),
\[
 \begin{aligned}
 \|(1+r^2)(Q(X)-Q(Y))'\|_2
 &\le B_{uv}\,J,\\
 B_{uv}&:=3K^2+3\sqrt\pi\,K
                     \left(\frac{\sqrt\pi}{2}+H_v\right),\\
 \|(1+r^2)Q(X)\|_\infty&\le K^3,\qquad
 \|(1+r^2)Q(X)'\|_2\le
          3K^2\left(\frac{\sqrt\pi}{4}+H_u\right).
 \end{aligned}\tag{N28}
\]
Here **there is no nonintegrable
\(\|(1+r^2)W'\|_2\) term**:
the exact \(W\) or \(W^2\) factors from
the original cubic difference remain present.

Differentiating the *real original Riesz convolution* in (N26)
and applying (N25)–(N28) now proves
\[
 \boxed{\begin{aligned}
 &\|(1+r^2)\partial_r[
   \mathcal N_{\rm H}(W+u)-\mathcal N_{\rm H}(W+v)]
   \|_{L^2(dr)}\\
 &\quad\le
  (24C_{\rm A2}K^6+9K^2)D
  +3K^2A_{uv}\Bigl(\frac{\sqrt\pi}{4}+H_u\Bigr)\\
 &\qquad\quad+
 \Bigl[(3+A_v)B_{uv}
       +36\sqrt\pi\,C_{\rm A2}K^5U_v\Bigr]J ,
 \end{aligned}}\tag{N29}
\]
together with
\[
 \boxed{\quad
 \|\mathcal N_{\rm H}(W+u)-\mathcal N_{\rm H}(W+v)\|_{L^2(dr)}
 \le A_{uv}K^2(\sqrt{\pi/2}+U_u)
          +3(3+A_v)K^2D .
 \quad}\tag{N30}
\]
For clarity, the new mixed term
\(36\sqrt\pi\,C_{\rm A2}K^5U_v J\)
comes from the **nonlocal real derivative**
\(\partial_r[P_Y-P_W]\) multiplied by
\((1+r^2)[Q(X)-Q(Y)]\); it is not dropped
as in a local-NLS surrogate.

For \(H_u,H_v,U_u,U_v\) bounded by a fixed
\(R_*\), the explicit coefficients in
(N29)–(N30) are bounded by a polynomial
\(C(R_*,C_{\rm A2})\) and
\(A_{uv}\lesssim_{R_*}D+J\). Thus the
actual original quartic Hartree map is
**locally Lipschitz**
\[
 \boxed{
 \|\mathcal N_{\rm H}(W+u)-\mathcal N_{\rm H}(W+v)\|_2
 +\|(1+r^2)\partial_r[
    \mathcal N_{\rm H}(W+u)-\mathcal N_{\rm H}(W+v)]\|_2
 \le C(R_*,C_{\rm A2})(D+J).
 }\tag{N31}
\]

**Precise §2.13 status:** this is a genuine *spatial
nonlinear source* Lipschitz estimate derived directly
from the original Hartree PDE and two actual
correction fields. For a moving parameter \(\alpha\),
it applies to \(u_\alpha-u_\beta\) once the PDE
constructs those fields and proves **their**
parameter-Lipschitz control in \(D+J\).
It does not construct the parameter-dependent
corrections, prove a time-positive source order,
or bound the remaining Laplacian/moving-cutoff terms.
The projected Hartree homogeneous adjoint Kato
inverse and physical orbit remain OPEN.
It is a human paper theorem invoking an externally
published weighted \(A_2\) result, not a
new Lean CI or axiom. Original **11/13** unchanged.
