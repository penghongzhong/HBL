# HBL 2.13 — selected exterior envelope and original-input feedback

Date: 2026-11-05. Revised manuscript count remains **11/13 (84.62%)**. This is a completed source-envelope bridge and finite-annulus spatial synthesis, not acceptance of the complete finite-profile theorem.

## Strict acceptance

- Immutable proof commit: `38fc0f275766093eada7904385a1444a39591eef`.
- Successful workflow: [41968947520](https://github.com/penghongzhong/HBL/actions/runs/41968947520), job `127052405410`; all steps completed successfully.
- Evidence artifact: `13389296155`, `hbl-213-exterior-feedback-audit`.
- Downloaded ZIP SHA-256: `5dfef3f665c4081132e8eb5e9f64a3e3ec2dd979f3e42214e6b79424be31e3c3`.
- Lean `4.35.0-rc3`, compiler `470d5ce1400764999581fd26d5d72b00d990b0f4`; Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.

Six new public theorems in two new files were added. The final workflow strictly replayed **five target files and audited eleven public declarations**, including the previous three exterior files. All five `--trust=0 -DwarningAsError=true` replay logs are empty. All eleven full-type reports are present without truncation, and each transitive axiom report contains exactly `propext`, `Classical.choice`, `Quot.sound`. The audit log is 173297 bytes.

After downloading the ZIP, a separate local script checked its SHA-256, the exact commit, all five source SHA-256 values and Git blob identifiers, the two retained new source byte strings, empty strict logs, the declaration list, the complete type output and the axiom allowlist. This is **remote targeted Lean verification plus local archive inspection**, not a fresh local Lean replay or a re-audit of every historical manuscript environment.

New immutable blobs:

- `ActualHartreeMatchedExteriorEnvelope.lean`: `72c1759f510248f1767a17cb7d1a373964fd2948`.
- `ActualHartreeMatchedExteriorSelected.lean`: `cced9159681d018af96e57a2c8725dd46fa5c2cc`.

## Reuse actually performed

The proofs call existing results directly: the moment-locked profile closeness estimate, `bubble_two_speed_tail`, continuity of the radially conjugated speed sources, the general-source unique compatibility correction, the quantitative complete inverse, the same normalized baseline trace estimate, the complete outer Green coefficient bound, and `actual_Hartree_matched_exterior_core_feedback`.

No Fredholm inverse, Kummer basis, kernel integral or independent exterior field was rebuilt. Positive-radius continuity was recovered by dividing the already continuous conjugated source by radius on a local cutoff plateau; this also removes a separate corrected-source continuity premise from the new terminal.

## Mathematical result

Fix the actual origin-normalized Kummer pair, its coefficient and basis bounds, and a small endpoint `0 < B <= 1`. The displayed existing small-B condition is retained. Constants below may depend on this fixed basis data; they are independent of the input source functions and of the varying physical scale parameters in the stated region. Uniformity along moving Kummer parameters is not claimed.

Let

\[
N_0=\|F_{+,0}\|_{L^{2,7/4}}+\|F_{-,0}\|_{L^{2,7/4}},\qquad
|F_0(r)|\le Q_0/r^2\quad(L/a\le r\le B),\qquad Q_0\ge0.
\]

The inner sources are continuous and in the original weighted space. The outer RHS is interval integrable; the final feedback theorem also assumes its continuity at positive radii in the actual basis interval. These are raw source hypotheses, not an assumed estimate for an unknown correction.

The same complete compatibility matrix selects a unique real pair `(delta_b,delta_omega)`. Its adjusted outer source is exactly

\[
F_{\rm adj}(r)=F_0(r)-\delta b\,a^2 P_b(c,ar)-\delta\omega\,a^2 P_\omega(c,ar).
\]

Here `P_b=i*(Lambda V_c-c*d_c V_c)` and `P_omega=V_c`; the monopole remains moment-locked.

### Actual speed-source envelope

The genuine bubble tails and actual O(|c|) profile closeness prove

\[
|a^2P_b(c,ar)|,\ |a^2P_\omega(c,ar)|
\le C_{\rm sp}aB/r^2
\]

for `L>=1`, `a>0`, `B<=1`, `a|c|<=1`, and `L/a<=r<=B`. Thus the constructed envelope

\[
Q_{\rm adj}=Q_0+C_{\rm sp}aB(|\delta b|+|\delta\omega|)
\]

bounds the **entire** corrected RHS. The cost is aB rather than a squared.

### Selected envelope controlled by original inputs

`actual_Hartree_selected_corrected_source_bounds_region` constructs common `L0`, `epsilon`, `C`, with `L0>=6` and `0<epsilon<=1`. Under

\[
L\ge L_0,\qquad a\ge L^3,\qquad a|c|\le\epsilon,
\]

it selects the unique compatible pair and constructs a nonnegative `Q_adj` satisfying the envelope and

\[
\boxed{N_{\rm adj}+Q_{\rm adj}\le C(N_0+Q_0).}
\]

The aB factor cancels against the actual inverse's `1024/(a B^2)` bound. The complete obstruction is bounded using the SAME original Fredholm jet and full Green forcing integral. No bound for Z, selected speed, adjusted norm, or adjusted envelope is a premise of this synthesis.

### Actual feedback after that SAME selection

`actual_Hartree_selected_exterior_feedback_region` applies the earlier actual-annulus theorem to these exact adjusted sources and their fixed normalized inverse. It constructs the matched field `w_adj` from their actual jet and defines `q_adj(y)=y Re w_adj(y/a)`. It proves absolute interval integrability and

\[
\boxed{\left|\int_L^{aB}K_H(r,y)q_{\rm adj}(y)\,dy\right|
\le C_*(N_0+Q_0)L^{-2}\,rW(r)^3,\qquad 0<2r\le L.}
\]

This closes the previously explicit gap that the feedback theorem required adjusted sizes while the source correction only bounded the adjusted inner norm. The RHS now contains only original input sizes.

## Remaining obligations

The interval is still `[L,aB]`. Nothing beyond aB is set to zero. This is not yet the full nonlocal difference for the globally glued field: transition-annulus terms, subtraction of the original inner tail, and the remote contribution must be joined and measured in the actual manuscript residual norm.

The original input norm/envelope must also be produced for each actual PDE residual iterate. Actual time derivatives, moving parameters and interfaces, Hessian changes, nonlinear remainders, infinity radiation matching and the finite recurrence are not consequences of this frozen spatial estimate. Physical entry into and persistence in the parameter region remain obligations. The type-II rate must be derived from the actual dynamics, not prescribed.

No new manuscript environment is accepted by this record. The revised total remains **11/13**.

## Debug record

The failed builds are not acceptance evidence. Repairs qualified an ordered-sum lemma and removed a tactic after an already closed field identity. They did not change hypotheses or add axioms. Final acceptance is the immutable run and commit recorded above.
