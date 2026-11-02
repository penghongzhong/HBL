# HBL revised 2.13: short real-Hartree mixed source dependency ledger (2026-11-02)

## Exact strict history (do not inflate manuscript numerator)
- `41478947464` completed/success (offterminal single-PDE-orbit nonlocal moving-cutoff weighted (L^{2,\sigma}), for (3/2<\sigma<2)): `actual_one_Hartree_orbit_offterminal_full_nonlocal_weighted_Riesz_gain`.
- `41480066238` completed/success (single true-PDE-orbit quartic mixed quadratic/higher uniform (O(\ell))): `actual_one_Hartree_orbit_offterminal_mixed_higher_uniform_gain`.
- `41476491255` completed/success (exact physical radial frozen Kummer conjugacy): `actual_Hartree_Kummer_frozen_operator_physical_conjugacy`.
- `41477143513` completed/success (offterminal mixed quadratic/cubic pointwise source).
- `41535997000` completed/failure due to five instances of `bubble` not in the open namespace; repaired without modifying theorem statement (commit `f7b075a0`) and re-run `41537951421`.
- `41537976655`: new full mixed Riesz bubble-squared majorant under strict CI; check final verdict.
- `41539793779`: actual full mixed Hartree potential × moving-monopole cubic source pointwise weighted gain under strict CI; check final verdict.
- `41539834937`: weighted (L^2) `MemLp` theorem under strict CI; check final verdict.

All candidate branches remain outside main pending successful types/axioms and mathematical scope audit. No new axiom/sorry/admit accepted.

## Single-short-chain analytic target
The physical equation is the real 3D inverse-square generalized Hartree PDE, with nonlocal density `|u|⁴` and local cubic factor `|u|²u`. For one regular PDE orbit (z(t,r)), set
```math
Z_\ell(t,r)=\sqrt\ell\,z(t,\ell r),\qquad
c(t,\ell)=\kappa_H\ell\,m[z(t)],\qquad
V_c(r)=W(r)+c(1-\chi(|c|r/4))\Phi_{\rm mon}(r).
```
The imported true Hartree local-flow / Strauss interfaces must supply a fixed time window, a uniform pointwise bound `B`, a radial Strauss constant `A`, and physical moment continuity. These are not claimed from critical (H^1) local wellposedness alone.

Proposed core estimates, each to be matched with actual Lean proofs:
```math
(1+r)|V_c(r)|\le D:=2+9C_{\rm mon},
\quad (1+\ell r)|Z_\ell(t,r)|\le E\sqrt\ell,\ E=2(B+A),
```
```math
F_{\rm mix}=|V_c+Z_\ell|^4-|V_c|^4-|Z_\ell|^4,
\qquad
|F_{\rm mix}(r)|\le
(4D^3E+6D^2E^2+4DE^3)\sqrt\ell\,W(r)^2.
```
```math
|\mathcal I F_{\rm mix}(r)|\le
C_{\rm Riesz}(4D^3E+6D^2E^2+4DE^3)\sqrt\ell,
```
```math
w_\sigma(r)|V_c(r)|^3\le D^3W(r),\quad \sigma\le2,
```
```math
\|w_\sigma(\mathcal I F_{\rm mix})V_c^3\|_{L^2(0,\infty)}
\le C\sqrt\ell\sqrt{\pi/2}.
```
The final quantitative (L^2) inequality is the analysis target, NOT yet an accepted Lean numeric-norm theorem. Current candidate establishes source `MemLp` and a pointwise (O(\sqrt\ell W)) majorant separately. The actual full nonlinear Hartree residual also contains the pure radiation self-Riesz term, the changes in local cubic factor, moving cutoff derivatives, parameter tangents and remote radiation; **none of those is silently dropped**.

## Acceptance blockers (retained manuscript)
1. Prove the same physical Hartree PDE source has strict positive order for ALL generated terms, not only the mixed quartic Riesz × (V_c^3) component.
2. Construct a globally valid normalized Kummer/remote correction; the canonical normalized Green inverse uses all homogeneous freedom. The outer (C^1) interface conditions cannot be assumed from inner data.
3. Complete real finite-profile recursion with actual source/parameter compatibility and the PDE-reconstructed main solution.
4. Derive the Type-II blowup scale from the actual modulation dynamics. Never assume a prescribed rate.

## Counting integrity
The last public retained-13 ledger (`verification/retained-original-13-mainchain-scope-audit-20261101.json`) records **9/13**, and historical original **9/21**. Later dialogue reports **11/13** but the public ledger has not been reconciled with explicit numbered amended manuscript definitions and a same-commit strict accepting terminal. Treat **11/13 as unverified** in formal public status until the revised TeX/environment map and CI report resolve this discrepancy. Passing an auxiliary theorem or revising the denominator alone never increases the numerator.
