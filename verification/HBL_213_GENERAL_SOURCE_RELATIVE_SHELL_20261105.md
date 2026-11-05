# HBL 2.13 — arbitrary coherent sources and a genuine relative matched-shell bound

Date: 2026-11-05. Revised manuscript count remains **11/13 (84.62%)**. This round accepts a reusable source-to-matched-shell theorem, not the complete finite-profile construction. Earlier eleven manuscript environments have not been re-audited in this run.

## Strict acceptance

- Immutable proof commit: `9e953a33e44e5fdea1f8d3bb74cf17719bddbb87`.
- Successful workflow: [41939172176](https://github.com/penghongzhong/HBL/actions/runs/41939172176), job `126955232368`, all steps successful.
- Evidence artifact: `13376080330`, `hbl-213-general-source-audit`.
- Downloaded ZIP SHA-256: `7158bc187b7c476dc59d9ab39d956cc690b828fc6848c9d69c72d09149427a4b`.
- Lean `4.35.0-rc3`, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`; Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.

Two new source files were replayed with `--trust=0 -DwarningAsError=true`; both strict logs are empty. Four public declarations have full, untruncated type reports and transitive axiom reports containing exactly `propext`, `Classical.choice`, `Quot.sound`. The downloaded audit log has 100919 bytes. ZIP hash, source SHA-256 values, immutable Git blob identifiers and locally retained source bytes have been independently checked. This is targeted strict replay, not a fresh strict replay of every historical dependency. Existing dependency warnings are not claimed to have been removed.

The two checked blobs are:

- `ActualHartreeGeneralSourceCorrection.lean`: `0c735d198c38e99109774876dfe78256a015dc6f`.
- `ActualHartreeGeneralMatchedShell.lean`: `c41489f0cdb32fb589ca59779352a820ce1dcd88`.

The earlier correction-only run `41938424926` succeeded. The first shell integration `41938695533` failed at one algebraic normalization of the base physical source. The accepted repair unfolds that same physical source on both sides; it changes no hypotheses or mathematical target.

## Why this is different from the earlier base-source bound

The previous obstruction estimate was specialized to the first core/radiation interaction and its absolute scale bound. That result could not automatically be applied to the residual produced by the next correction. The new terminal accepts arbitrary source functions in a specified, explicit class and measures the shell error relative to their actual input size.

Let

\[
N_0=\|F_+\|_{L^{2,7/4}(dr)}+\|F_-\|_{L^{2,7/4}(dr)},\qquad
\|F(r)\|\le Q/r^2\quad(L/a\le r\le B),\quad Q\ge0.
\]

Here `F` is the **entire outer correction RHS**, not a projection, replacement scalar or assumed small obstruction. The input requires continuous inner sources in the original weighted space, interval integrability of F, and the stated positive-interval regularity for the corrected outer source. Q is a homogeneous size bound for the raw source. No particular power of ell or time-decay law is assumed.

Fix an actual origin-normalized Kummer pair with the verified coefficient/basis bounds D,G and small positive B. The terminal constructs common constants L0, epsilon, C, independent of the source functions and Q. Its physical region is

\[
L\ge L_0,\qquad a\ge L^3,\qquad a|c|\le\epsilon,\qquad 0<\epsilon\le1.
\]

The needed bounds `|c|<=1`, `L|c|<=1`, and `0<L/a<=B` are derived from this region. The basis data are explicit inputs already supplied by the preceding basis theory. This run does not claim a new source-independent basis construction or uniform differentiability along moving Kummer parameters.

## 1. Complete obstruction and unique correction for arbitrary inputs

`actual_general_source_Green_coefficient_bound` uses the exact Wronskian to prove

\[
\|\operatorname{GreenCoeffA}(K,B,F;L/a)\|
\le [1+(D+1)GB^2]BQ.
\]

With the already verified actual normalized baseline trace, this bounds the complete obstruction by

\[
\|Z\|\le (C_T/a)N_0+[1+(D+1)GB^2]BQ.
\]

`actual_Hartree_general_source_correction_region` then constructs the unique real pair p=(db,dw) satisfying the full coupled compatibility equation, using the same baseline Fredholm jet, same basis, and same outer source. For

\[
F_+^p=F_++d\omega\,G_\omega,\qquad
F_-^p=F_-+db\,G_b,
\]

it proves

\[
\boxed{\quad
N_{\rm adj}\le N_0+C_{\rm corr}L^{-1/2}(N_0+Q).
\quad}
\]

Neither a speed-inverse bound nor an estimate of Z is a premise. They are produced by the existing full-matrix theorems and the actual source bound.

## 2. The source identity is exact and is preserved by the physical speed directions

For the overlap [L/2,L], the required source coherence is

\[
a^{-2}F(y/a)+\frac{F_+(y)+iF_-(y)}y=0.
\]

This is an identity between two representations of the same forcing, not an error bound. The public theorem `actual_Hartree_general_radial_partition_coherent` proves it for the natural partition of **any** complex physical source S:

\[
F_+(y)+iF_-(y)=y\eta_L(y)S(y),\qquad
F(r)=-a^2S(ar),\qquad \eta_L=1-\chi(\cdot/L).
\]

The cutoff is one throughout the overlap. A further kernel-checked helper proves that adding the actual scale/phase inner inputs and subtracting their full outer RHS directions preserves this exact coherence. No free affine charge, independently chosen trace or interface repair forcing is introduced.

## 3. Actual matched fields and a relative shell gain

The main new terminal is `actual_Hartree_general_source_matched_shell_region`. It constructs the unique p, the same normalized Fredholm outputs and the explicit matched Kummer field. The common actual Cauchy jet at y=L is proved from these fields. The corrected exterior source is retained on the complete interval and continued backwards over [L/2,L].

Let R=L/2, u be the actual inner physical field, v the matched Kummer pullback, d=u-v, and E_sh the commutator of the full scaled Kummer operator with the actual cutoff applied to d. This includes the Kummer first-order transport term. In the original radially conjugated source norm, the terminal proves

\[
\boxed{\quad
\|\mathbf1_{(R,2R)}\,r\,|E_{\rm sh}(r)|\|_{L^{2,7/4}(dr)}
\le C R^{-3/4}(N_0+Q).
\quad}
\]

The right-hand side contains neither an unknown compatibility defect nor an adjusted-source norm. The constant is chosen before the arbitrary source data. The same constructed exterior field also has zero actual outgoing trace at the finite endpoint B.

For L=ell^(-1/16), the relative factor R^(-3/4) is 2^(3/4) ell^(3/64). This elementary algebraic consequence is not counted as another Lean declaration. The estimate is source-relative rather than an absolute estimate for one fixed base interaction.

## Scope needed for the remaining main-chain step

The theorem now applies to any later residual **once that residual is shown to satisfy its explicit source-space, regularity and coherence requirements**. It does not assert those requirements for all nonlinear iterates automatically.

In particular, `N0+Q` is the displayed input size, combining the original inner weighted norm with a radius-squared outer envelope. Its control by the manuscript's full scaled norm X_f^sc for every generated residual remains an obligation; no such equivalence is assumed or claimed here.

The result controls the actual overlap commutator, not the entire PDE residual after patching. The same global correction still requires estimates for Hartree nonlocal feedback, its actual time derivative, moving parameters/Hessian differences, nonlinear remainder, and remote matching. A zero trace at finite B is not an infinity radiation condition. These terms and the true norm interfaces must be closed before using the finite recursion as a PDE construction.

No hstep, generated-term order label or assumed Type-II rate replaces these missing estimates. The dynamical-rate main target is unchanged. Formal manuscript count stays **11/13**.
