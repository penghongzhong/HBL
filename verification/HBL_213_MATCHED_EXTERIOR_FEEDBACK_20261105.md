# HBL 2.13 — matched exterior growth and finite-annulus core feedback

Date: 2026-11-05. Revised manuscript count remains **11/13 (84.62%)**. This round verifies a new spatial component, not the full finite-profile theorem. Earlier manuscript environments are not re-audited here.

## Strict acceptance anchor

- Exact proof commit: `2487fdc087b098a90616870dd8c4720896720965`.
- Successful workflow: [41960144828](https://github.com/penghongzhong/HBL/actions/runs/41960144828), job `127024325346`; all steps successful.
- Evidence artifact: `13384309871`, `hbl-213-exterior-feedback-audit`.
- Downloaded ZIP SHA-256: `f32b7a82e10d0437d318bc3d7b5b90606c3f212f510b9bcb3bbaf15a6e2bc3b4`.
- Lean `4.35.0-rc3`, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`; Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.

All **five public declarations in three target files** passed `--trust=0 -DwarningAsError=true` with empty target-source replay logs. The full-type and transitive axiom log is 31,573 bytes, with no truncation, warnings, errors or sorryAx. Every public declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

The downloaded ZIP, exact commit, three source SHA-256 values, Git blob identifiers, local retained source bytes and empty replay logs were independently checked. The immutable GitHub file responses confirm these blob IDs:

- `ActualHartreeMatchedExteriorGrowth.lean`: `174f4788b4a60e71d5277bebff1411917b192142`.
- `ActualHartreeMatchedExteriorKernel.lean`: `86dfe0ae73464148ddfc4d6c83caaa87f3fb5bd0`.
- `ActualHartreeMatchedExteriorTail.lean`: `46090f43fcc3c53ec112ca553c543e7f341c08dd`.

This is targeted strict replay of these three sources, not a new strict replay of all historical dependencies. Historical dependency warnings are not claimed to have been removed. Earlier growth-only workflow `41955406543` also succeeded and was independently checked; the final acceptance above includes that producer together with the actual kernel and final feedback theorem. Failed debugging runs are not acceptance evidence.

## Mathematical scope

The same normalized Fredholm inner jet, the same matched Kummer field, and the original Hartree kernel are used throughout. Let

\[
N=\|F_+\|_{L^{2,7/4}}+\|F_-\|_{L^{2,7/4}},\quad r_0=L/a,
\quad J=\operatorname{CanonicalInnerJet}(F_+,F_-;a,r_0).
\]

Let F be the full outer RHS, with \(|F(z)|\le Q/z^2\) on \([r_0,B]\), and let

\[
w(z)=\operatorname{actualOriginMatchedKummerValue}(K,r_0,B,F,J_1,J_2;z),
\qquad q_{\rm ext}(y)=y\operatorname{Re}w(y/a).
\]

The source class explicitly requires continuous inner sources in the genuine weighted space, positive-interval continuity of F, and the same actual origin-normalized basis bounds. The exterior theorem has L>2, a>0, L/a<=B<=1, B<scale. It does not assume a particular time law.

### Actual exterior growth

`actual_matched_Kummer_forward_formula` proves the exact forward representation before estimating the singular basis contribution. It retains the actual left Cauchy data and the integrals from r0 to the observation point, rather than replacing them by unrelated outgoing data.

`actual_matched_Kummer_outward_growth` proves

\[
|w(z)|\le C_g\bigl(|J_1|+r_0|J_2|+Q\bigr)\,z/r_0.
\]

The conservative observation-radius factor z/r0 is retained. This is **not** a radius-independent boundedness statement for w. The exact forward formula avoids an artificial fixed B/r0 multiplier near the inner interface; the displayed estimate still grows toward the outer endpoint.

`actual_Hartree_canonical_inner_jet_size` proves for the same actual normalized outputs

\[
|J_1|+r_0|J_2|\le(C_{\rm val}+C_{\rm der})N.
\]

Consequently, with C_e determined by the fixed basis bounds and fixed inverse constants,

\[
|q_{\rm ext}(y)|\le C_e(N+Q)y^2/L\quad(L\le y\le aB).
\]

### Actual finite-annulus Hartree feedback

`actual_Hartree_quadratic_annulus_kernel_bound` integrates the original separated Hartree kernel, including absolute integrability, for a finite annular datum bounded by M y^2/L.

`actual_Hartree_matched_exterior_core_feedback` applies that result to the SAME actual field above and proves

\[
\boxed{\quad
\left|\int_L^{aB}K_H(r,y)q_{\rm ext}(y)\,dy\right|
\le32\pi\kappa_H C_e(N+Q)\frac{rW(r)^3}{L^2},
\qquad0<2r\le L.
\quad}
\]

The scalar estimate

\[
\frac1L\int_L^{aB}y^{-2}\,dy\le L^{-2}
\]

explains why the upper endpoint does not enter the bound. No exterior growth hypothesis is left in the final actual-field theorem: growth is derived from J, F and the existing source-space estimates. Under the existing choice L=ell^(-1/16), the coefficient L^(-2) equals ell^(1/8); this last algebraic specialization is not separately counted as a new Lean theorem in this run.

## Exact remaining obligations

This is the contribution of **[L,aB] only**. The field is not set to zero for y>aB. This is not yet the full difference between the nonlocal action on the global glued field and that on the original inner solution. The transition annulus, old inner-tail subtraction, remote tail and the measurement in the original PDE residual norm remain to be joined.

For application after the compatibility speed correction, F is the corrected full RHS and Q must be its actual envelope Q_adj. The existing bound for N_adj does not by itself establish Q_adj<=C(N0+Q0). That source-envelope bridge must be proved for the same selected real speed pair; it is not silently assumed here.

There is a concrete next estimate to formalize. On r in [L/a,B], the actual speed-profile bounds and a|c|<=1, B<=1 give r^2 |a^2 P_c(ar)|<=C aB. Hence Q_adj<=Q0+C aB(|delta b|+|delta omega|). Combining the already proved complete inverse and obstruction estimates should control this by the original source sizes. This paragraph is a paper-level continuation target, not additional strict acceptance.

Time derivatives, varying parameters/Hessian, nonlinear Taylor remainder and infinity radiation matching are not consequences of this frozen spatial theorem. No finite-profile environment or type-II blowup main theorem is counted as accepted by this module. The concentration rate must still be derived from the actual dynamics, not prescribed. Revised manuscript count remains **11/13**.

## Implementation record

The scalar kernel integral was separated from the large Fredholm module. A persistent elaboration bottleneck was localized to backward inference of a measurable composition, which expanded the Hartree kernel. The final proof constructs the measurable pair map first. The scalar antiderivative uses the pinned Mathlib integer-power integral. These are proof-implementation changes, not weaker hypotheses or extra axioms. No diagnostic trace remains in the accepted sources.
