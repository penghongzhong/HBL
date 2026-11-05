# HBL 2.13 — remote geometric Hartree error has strict positive time order

Date: 2026-11-05. Revised manuscript acceptance remains **11/13 (84.62%)**. This record closes the geometric part of the true remote Hartree mismatch; it does not claim that the scalar three-region center balance vanishes by itself.

## Strict acceptance

- Proof commit: `aa3207d77724004afa10b9655201abc3d334a6b6`.
- Workflow: [41975048188](https://github.com/penghongzhong/HBL/actions/runs/41975048188), job `127071820460`: **success**.
- Artifact: `13391572461`, `hbl-remote-geometric-time-audit`.
- ZIP SHA256: `241305ed67b9e7507f4e5a805ee0bdc06d68ca95ee7743bf54a7f1f8b0f6afbc`.
- Lean 4.35.0-rc3, compiler `470d5ce1400764999581fd26d5d72b00d990b0f4`; Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Three target source files passed `--trust=0 -DwarningAsError=true` with empty logs.
- Eight declarations were full-type / transitive-axiom audited. Every axiom report is exactly the standard set `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- The downloaded ZIP digest, exact commit, source SHA256 values and audit log were independently checked.

## Reuse actually performed

No new remote Hartree kernel argument was created. The proof reuses:
- `actual_fullHartree_effective_mismatch_norm_le` from `PhysicalSourceMismatch.lean`;
- the exact physical radius identity `R_c=4/|c|` and quadratic geometric gap from `ExteriorQuadraticSlowGain.lean`.

The new file only converts the already physical `c^2` gain into renormalized-time order.

## Result

Define
\[
\varepsilon_{\rm rem}(\beta)=2\beta-1.
\]
Lean proves
\[
\beta>\frac12\quad\Longrightarrow\quad \varepsilon_{\rm rem}(\beta)>0.
\]
If
\[
s\ge1,\qquad |c(s)|\le C s^{-\beta},
\]
then
\[
\boxed{c(s)^2\le C^2s^{-1-\varepsilon_{\rm rem}(\beta)}
=C^2s^{-2\beta}.}
\]

For the genuine remote quartic density \(F\), on a fixed normalized core \(0<r\le1\), the actual potential-center gap at the true monopole radius satisfies
\[
\boxed{
|P_F(R_c,r)-C_F(R_c)|
\le
\frac{\pi\kappa_H}{4}C^2
s^{-1-(2\beta-1)}r^2
\int_{R_c}^{\infty}|F(\rho)|\,d\rho .
}
\]

The full physical remote residual therefore splits into
\[
\text{remote mismatch}
=
\underbrace{|c-C_F|}_{\text{scalar three-region center balance}}
+
\underbrace{O(s^{-1-(2\beta-1)})}_{\text{strict geometric error}},
\]
up to the already explicit bounded local cubic factor.

## Important correction to the closure strategy

The scalar term \(|c-C_F|\) should **not** be forced to vanish for the remote component alone. The current code also proves
\[
c=\operatorname{actualRadiationCenter}(Z_\ell),
\]
the center mass of the **whole** physical radiation, while the exact three-region source identity splits that radiation between inner/Kummer and remote pieces. Thus the correct next closure target is the three-region center balance, not an artificial remote-only cancellation.

The repository already contains the exact same-PDE three-region identity, the physical Kummer source certificate, the off-terminal weighted Riesz gain and the phased-flat integrable tail. Those will be reused as the next producers.

No manuscript environment is newly accepted here. Revised count remains **11/13**.
