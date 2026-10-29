# HBL: physical monopole source-to-dynamical-rate bridge

Scope: this is a real (first-order radial) inverse-square Hartree threshold source, NOT the complete high-order PDE residual of a constructed blowup orbit. The original complete \`prop:one-layer-stage3\`, its finite-profile successor, and the full main PDE theorem are still open.

## Already strictly available

The file HBL/MonopoleComplexResidual.lean proves the on-core estimate (theorem \`monopoleComplexEffectiveIncrement_core_bound\`), for a genuinely constructed moving-cutoff profile:

\[
\|\mathcal R_{\rm eff}(s,r)\|
 \le C_{\rm st} c(s)^2
  + C_{\rm pr}|c_s(s)|
  + D\,|b(s)c(s)| + C_{\rm pr}|\omega(s)c(s)|
\quad(0<r<1,\; |c(s)|\le1).
\]

The files HBL/MonopoleCoreIntegrability.lean and HBL/MonopoleThresholdProjection.lean construct the **actual fixed normalized test** \(\zeta_+\), the genuine real projection \(F_{\rm mono}(s)\) and its absolute space/time integrability. No arbitrary residual measurable/integrable hypothesis is used in these original statements.

## Missing quantitative projection estimate: derive from the established pointwise estimate

Define \(Z_+:=\sup_{0\le r\le1}|r\zeta_+(r)|<\infty\). Compact support beyond \(r=1\) and the actual half-line-to-core identity imply

\[
|F_{\rm mono}(s)| \le
 Z_+\left(C_{\rm st}c(s)^2+
 C_{\rm pr}|c_s(s)|+
 D|b(s)c(s)|+C_{\rm pr}|\omega(s)c(s)|\right).
\]

For any \(\beta>\tfrac12\) and sufficiently late \(s\ge s_0\ge1\), the existing primitive decay assumptions

\[
|c(s)|\le A s^{-\beta},\quad
|c_s(s)|\le A s^{-1-\beta},\quad
|b(s)|+|\omega(s)|\le 2 A s^{-1}
\]

give

\[
|F_{\rm mono}(s)|\le
Z_+\left[C_{\rm st}A^2 s^{-2\beta}
+(C_{\rm pr}A+D A^2+C_{\rm pr}A^2)s^{-1-\beta}\right].
\]

Thus, with \(\delta_{\rm mono}=\min\{2\beta-1,\beta\}>0\),

\[
|F_{\rm mono}(s)|\le C_\star s^{-1-\delta_{\rm mono}},
\quad C_\star=Z_+\left(C_{\rm st}A^2+C_{\rm pr}A
+D A^2+C_{\rm pr}A^2\right).
\]

The full numerical constants and the exact \(\zeta_+\) normalization must be checked in Lean. This last quantitative estimate is a **mathematical candidate, NOT a completed strict Lean theorem**.

## Submitted Lean source in this branch

- HBL/TypeIIDynamicSelection/MonopoleRateDefinitions.lean: integrate the genuine physical first-monopole projected source, with no prescribed terminal value.
- HBL/TypeIIDynamicSelection/MonopoleRateLimit.lean: use real time-integrability to obtain its emergent scalar limit.
- HBL/TypeIIDynamicSelection/MonopoleRateTail.lean: assuming a quantitative source bound, derive the tail \(C_\star s^{-\delta}/\delta\).
- HBL/TypeIIDynamicSelection/MonopoleRateTrapping.lean: combine late-time source smallness with an initial open modulation margin to preserve \(\mu_\infty>9/16\), and hence faster-than-self-similar output rate.

The first strict Actions attempt is 40873755821. No result may be claimed before its completion.

## Crucial outstanding equation

To promote this mechanism to a **genuine dynamically selected HBL Type II blowup**, one must establish the projected modulation equality from an actual strong solution and its full finite-profile remainder, schematically

\[
\mathcal M_{\rm phys}(s)\binom{\mu_s}{\vartheta_s}
 = \Pi_{\rm phys}\left[
 \mathcal F_{\rm Hartree}(V_N+Q)-\mathcal F_{\rm Hartree}(V_N)
 \right]
 + \Pi_{\rm phys}\mathcal F_{\rm Hartree}(V_N),
\]

with \(\mathcal M_{\rm phys}\) invertible in the genuinely constrained space. The scalar \(F_{\rm mono}\) above covers only the first effective radial correction. Its integrability alone does **not** identify the exact \(\mu_s\), prove \(\mu_\infty\), or construct an actual PDE orbit.

No revised original manuscript theorem is declared closed. Historical original count remains **9/21**, target 20/21 after eleven real load-bearing environments are discharged or correctly replaced.
