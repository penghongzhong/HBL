# HBL revised §2.13: a fixed physical mass gauge fails in the presence of nonzero terminal radiation

10 November 2026 (America/Los_Angeles). **Paper-level quantitative obstruction; not a Lean acceptance.** Parent branch at analysis: \`hbl-213-spectral-c1-trace-20261109\`. The revised original manuscript count remains **11/13**. This note corrects the *possible* fixed-radius mass-gauge route in the exact mass/phase calculation (MG4)–(MG5); the underlying finite-radius flux identities remain valid.

## 1. Exact physical mass of the concentrating Hartree bubble

Let \(\ell>0\) denote the **physical shrinking scale**, and let
\[
W(y)=(1+y^2)^{-1/2},\qquad B_\ell(r)=\ell^{-1/2}W(r/\ell).
\]
For a fixed physical radius \(R>0\), the candidate gauge in (MG4) is
\[
M_R(u,\ell)=\tfrac12\int_0^R r^2\bigl(|u(r)|^2-B_\ell(r)^2\bigr)\,dr .
\]
The bubble contribution is **exactly**
\[
\boxed{\int_0^R r^2 B_\ell(r)^2\,dr
=\ell\bigl[R-\ell\arctan(R/\ell)\bigr]\le\ell R .}\tag{RG1}
\]
In particular, the bubble has vanishing local mass at any fixed physical radius during concentration. The same is **not** generally true of nonzero regular terminal radiation.

**Proposition (necessary zero-radiation condition for the fixed-radius gauge).** Let \(0<r_-<r_+<R\), \(\ell_n\downarrow0\), and suppose \(u_n\to z\) in \(L^2((r_-,r_+);r^2dr)\) with
\(m^2:=\int_{r_-}^{r_+}r^2|z(r)|^2dr>0\).
Then
\[
\boxed{\liminf_{n\to\infty}M_R(u_n,\ell_n)\ge\tfrac12m^2>0.}\tag{RG2}
\]
Indeed, positivity of the full physical local mass and (RG1) give
\[
M_R(u_n,\ell_n)
\ge \tfrac12\|u_n\|^2_{L^2((r_-,r_+);r^2dr)}
-\tfrac12\ell_n R ,
\]
and pass to the limit. **No sequence of roots \(M_R(u_n,\ell_n)=0\) can therefore exist.** Dividing the gauge by \(\ell_n\) does not change its roots. A continuous nonzero radiation profile \(z(r_*)\ne0\) supplies such an annulus around \(r_*\) whenever \(R>r_*\).

This is a theorem about local-mass geometry, not a constructed Hartree blowup orbit. The hypothesis of annular radiation persistence must be verified for the actual solution, rather than silently assumed. It nevertheless exposes a **missing existence premise** in the proposed use of (MG4)–(MG5): the nonzero-radiation HBL ansatz cannot use a fixed physical matching radius that encloses persistent nonzero terminal radiation. A nonvanishing scalar Jacobian at a hypothetical root does not establish that a root exists.

## 2. The correct geometric alternative is a shrinking physical interface

Put \(R_\ell=\ell L(\ell)\), \(L(\ell)\to\infty\), \(\ell L(\ell)\to0\).
For the exact profile \(u=B_\ell+z\) with \(|z(r)|\le M\) on \([0,R_\ell]\), the bubble local half-mass is
\[
M_{\mathrm{bubble}}(\ell,L)=\tfrac12\ell^2\bigl(L-\arctan L\bigr).
\]
The **genuine** radiation and bubble--radiation mixed masses satisfy
\[
\begin{aligned}
\frac12\int_0^{R_\ell}r^2|z|^2dr
&\le \frac{M^2}{6}\ell^3L^3,\\
\left|\Re\int_0^{R_\ell}r^2 B_\ell\overline z\,dr\right|
&\le\frac{M}{2}\ell^{5/2}L^2,
\end{aligned}\tag{RG3}
\]
using \(\int_0^L y^2(1+y^2)^{-1/2}dy\le L^2/2\).
For \(L\ge\pi\), division by \(M_{\rm bubble}\) yields
\[
\boxed{
\frac{|\text{mixed mass}|}{M_{\rm bubble}}
\le 2M\sqrt\ell\,L,\qquad
\frac{\text{radiation self-mass}}{M_{\rm bubble}}
\le\frac{2M^2}{3}\ell L^2.}\tag{RG4}
\]
On the original HBL inner interface \(L=\ell^{-1/16}\), these are
\(O(\ell^{7/16})\) and \(O(\ell^{7/8})\), respectively, **provided the true physical radiation remains bounded on the shrinking ball and the true remainder is separately controlled**. No independent Hartree source envelope or positive time gain is postulated.

## 3. A moving radius changes the scale Jacobian

At fixed physical \(u\), differentiation of the \(\ell\)-dependent gauge with \(R_\ell=\ell L(\ell)\) gives the *complete* derivative
\[
\boxed{\quad
\partial_{\log\ell}M_{R_\ell}(u,\ell)
=\ell^2 I(L)
 +\tfrac12 R_\ell^2
 \bigl(\partial_{\log\ell}R_\ell\bigr)
 \bigl(|u(R_\ell)|^2-B_\ell(R_\ell)^2\bigr),\quad
I(L)=\arctan L-\tfrac L2-\frac{L}{2(1+L^2)}.
\quad}\tag{RG5}
\]
In particular, if \(L=\ell^{-1/16}\) then \(\partial_{\log\ell}R_\ell=(15/16)R_\ell\). At the frozen exact bubble \(u=B_\ell\), the endpoint correction vanishes and \(\ell^{-2}L^{-1}\partial_{\log\ell}M_{R_\ell}=I(L)/L\to-1/2\).
For \(u=B_\ell+z\) with bounded \(z\), (RG3) similarly shows that the **endpoint Jacobian correction**, after division by \(\ell^2L\), is \(O(M\sqrt\ell L+M^2\ell L^2)\). This identifies a potentially well-conditioned *shrinking* scalar gauge, not a proved full Hartree modulation construction.

**Still OPEN:** actual selected-source remainder at the shrinking boundary, differentiation of the entire nonlocal Hartree PDE on the same orbit, compatibility with the uniquely selected **two** real Fredholm/Cramer speeds, real parameter Lipschitz, four-region time-positive residual, true finite profile, and PDE-derived Type-II rate. No new theorem was Lean-compiled. Original revised environments remain **11/13**.

**Strict historical scope rechecked:** CI 42927397872 (original four-piece PDE *identity*) and CI 42929423991 (three renormalized mass-phase *algebra* theorems) succeeded with Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, \`--trust=0\`, \`warningAsError\`, exact \`#check\`/\`#print axioms\`; their transitive axioms lie in \`propext\`, \`Classical.choice\`, \`Quot.sound\`. These jobs do not certify (RG1)–(RG5) or any new original theorem.
