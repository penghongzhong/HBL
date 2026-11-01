# HBL off-terminal flat radiation: non-prescribed-rate shortest proof path
Date: 2026-11-01. Status: mathematical proof plan, **NOT a Lean-accepted
original manuscript environment**.

## PRIMARY shorter route: off-terminal *spatial* flatness (manuscript 2.12)

The manuscript's actual high-regularity bounds in
\`eq:flat-bound-stage3\`, \`eq:flat-core-stage3\`, and
\`eq:flat-integrable-stage3\` require no terminal-time jet induction.
They follow **uniformly for every real physical time** from radial
$C^2$ regularity and the regular-flow Sobolev bound.

For $0\le r\le1$, a genuine $C^2$ radial scalar representative of the
physical $\mathbb R^3$ Hartree solution satisfies
\[
\partial_r z(t,0)=0,\qquad
\sup_{0\le r\le1}|\partial_r^2 z(t,r)|\le M
\]
for each admissible time $t$ and, under uniform high-regularity
Sobolev embedding, with the **same** $M$ on the regular-flow interval.
Two applications of the real-to-complex mean value theorem give
\[
|\partial_r z(t,r)|\le Mr,\qquad
|z(t,r)-z(t,0)|\le Mr^2,\qquad
|\partial_r^2z(t,r)|\le M.
\]
This is exactly the spatial quadratic remainder from the center value
$j_g(t)=z(t,0)$; the center is not assumed zero off-terminal.

Under the genuine critical pullback, with
$\ell(s)=\lambda(s)^{-1}>0$ and $t_s=\ell^2$, for
$0\le \ell(s)R\le1$,
\[
Z^{\flat}(s,R)
 =e^{-i\gamma(s)}\ell(s)^{1/2}
  [z(t(s),\ell(s)R)-z(t(s),0)],\qquad
|Z^\flat(s,R)|\le M\ell(s)^{5/2}R^2.
\]
The phase has modulus one. The original trap
$\lambda(s)\ge C^{-1}s^{\beta_-}$ yields
$\ell(s)\le Cs^{-\beta_-}$. For
$R\le s^{\rho_*}$ with
\[
\tfrac12<\beta_-<1,\qquad
0<\rho_*<\min\{\tfrac12,(5\beta_- -2)/4\},
\]
derive, without prescribing the terminal concentration exponent,
\[
|Z^\flat(s,R)|\le
 M C^{5/2}s^{-5\beta_-/2+2\rho_*}
 =MC^{5/2}s^{-1-\epsilon_{\rm flat}},
\quad
\epsilon_{\rm flat}=5\beta_-/2-2\rho_*-1>0.
\]

**Lean status:** \`ActualRadialSpatialFlatness.lean\` on branch
\`hbl-offterminal-spatial-flatness-20261101\` implements both MVT
steps and the *literal* rescaling identity, without assuming the
quadratic conclusion. Its strict CI is
https://github.com/penghongzhong/HBL/actions/runs/41308041077;
the result is pending until that CI succeeds.

**Critical still-unproved realization:** specialize Mathlib's
$H^L(\mathbb R^3)\hookrightarrow C_b^2$ (for $L>7/2$) to the
*cited external regular Hartree local theory's actual flow*, prove
that its radial representative is even and $C^2$ at the origin,
and supply a uniform $M$ across the chosen time interval and
finite time jets. Then formally combine with the already accepted
kinematic trap and source estimates. This is an ordinary spatial
Sobolev/regularity interface; it is far shorter than independently
proving arbitrarily high terminal time jets.

The independent higher time-jet proof route below is supplementary
for stronger terminal vanishing, **not a prerequisite for the
quadratic off-terminal flatness needed by original 2.12**.

## Supplementary: actual PDE and local terminal time-jet induction

Let $z(t,r)$ be a classical radial solution of the *genuine* 3D
energy-critical Hartree PDE on a terminal time interval, with
$P[z](t,r)=\kappa_H (|x|^{-2}*|z(t)|^4)(r)$ and
\[
 i z_t+(\partial_r^2+2r^{-1}\partial_r)z+P[z]|z|^2z=0
 \quad(r>0).
\]
Choose the actual real, smooth, nonzero annular terminal datum $g$
from \`ActualOneOrbitTerminalRadiation.lean\`, supported in
$[1/4,4]$, and set $z(T)=g$.

**Claim (finite time jets at the flat core).** Suppose all time/spatial
derivatives appearing below exist, commute, and the genuine Hartree
potential is sufficiently time-differentiable. For every
nonnegative integer $j$ in the available regularity budget,
\[
\partial_t^j z(T,r)=0,\qquad 0<r<1/4.
\]
Proof by induction. It is true for $j=0$. Differentiating the original
equation $j$ times gives
\[
 i\partial_t^{j+1}z
 =-\Delta_r\partial_t^j z-
 \sum_{k=0}^{j}\binom jk
  (\partial_t^k P[z])\,
  \partial_t^{j-k}(|z|^2z).
\]
The spatial Laplacian of the identically zero function
$\partial_t^jz(T,\cdot)$ vanishes on the open core. All derivatives
of $|z|^2z$ through order $j$ vanish there because the cubic is a
polynomial in $z,\overline z$ and each factor at time-jet order at most
$j$ is zero. No assertion that $P[z](T,\cdot)$ vanishes is needed.
Thus $\partial_t^{j+1}z(T,r)=0$.

Already strictly accepted: the $j=1$ core jet using the true PDE,
\`ActualOneOrbitTerminalPDEJets.lean\`; the $j=2$ extension is under
separate strict CI repair and must not be counted until its run succeeds.

## Uniform compact-core Taylor remainder

Fix $K=[r_-,r_+]\Subset(0,1/4)$ and integers $N,k\ge0$.
Assume the actual classical flow gives
\[
\sup_{\substack{T-\tau\le t\le T\\r\in K}}
|\partial_t^{N+1}\partial_r^k z(t,r)|\le M_{N,k}.
\]
The just-proved zero jets and integral Taylor remainder yield, uniformly
on $K$,
\[
|\partial_r^k z(t,r)|
 \le \frac{M_{N,k}}{(N+1)!}(T-t)^{N+1}.
\]
This is a theorem to formalize by a Banach-valued Taylor bound / repeated
FTC; **do not introduce the conclusion as a data hypothesis**.

The existing high-regularity Hartree flow interface in
\`RegularRadiationFlow.lean\` supplies explicit finite Sobolev time-jet
bounds, with an external classical local-theory boundary. Required
new Lean work: convert the actual Sobolev budget to a compact-core
uniform derivative bound by Sobolev embedding, and verify commutations
and potential differentiability for the *same PDE flow*.

## Physical rescaling, no prescribed blowup exponent

Let $\ell(s)=\lambda(s)^{-1}>0$ and
$Z(s,r)=\ell(s)^{1/2} z(t(s),\ell(s)r)$, where
$t_s=\ell^2$ is the genuine Hartree physical clock. If the moving
core satisfies $\ell(s)r\in K$,
\[
|\partial_r^k Z(s,r)|
\le\frac{M_{N,k}}{(N+1)!}
 \ell(s)^{k+1/2}\,\tau(s)^{N+1},
\qquad \tau(s)=T-t(s).
\]
If $t(s)\uparrow T$ and $\ell^2$ is tail-integrable, then
\[
\tau(s)=\int_s^\infty \ell(\sigma)^2\,d\sigma.
\]
This formula is derived from the clock by FTC and the *actual* terminal
time limit, not an assumed value of $\mu_\infty$ or a prescribed
$\ell(s)\sim s^{-\gamma}$.

To finish original 2.12, this flatness must be coupled to the verified
physical Hartree mixed-source estimates and the true projected
$H_\pm$, origin Kummer, and remote inverse on a common profile. The
complete generated-term gain and moving cutoffs still require proof.

**Acceptance ledger unchanged: 9/13 retained original environments,
9/21 historical. No sorry, admit, axiom, or fake direct PDE source
is introduced by this note.**


### Origin-inclusive core (essential physical regularity check)

The radial Lean jets currently apply to $0<r<1/4$ only. For
**uniform estimates down to $r=0$**, one must apply the above induction
to the genuine smooth $\mathbb R^3$ Hartree PDE on the open ball
$B(0,1/4)$ and the compact ball $\overline B(0,r_0)$, $r_0<1/4$.
In full space $\Delta$ is nonsingular, and the Hartree nonlinearity
still has the same pointwise cubic factor. The full 3D radial lift,
smoothness at the origin, and its agreement with the existing radial
representative are analytic/Lean obligations. Do not extrapolate
the current positive-radius radial theorem uniformly to $r=0$
without them.
