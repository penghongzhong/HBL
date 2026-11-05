# Reuse-first source register — 2026-11-05

## Produced and independently checked in this round

Source-inventory workflow 41963799924 completed successfully at commit `198ada08e685b365cf12401750465f888e5c6454`. This workflow **does not compile Lean or accept a mathematical theorem**.

- HBL selected working branch: `hbl-213-conjugated-two-weight-integrated-20261103`.
- HBL inventory commit: `198ada08e685b365cf12401750465f888e5c6454`.
- Mathlib inventory commit: `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Both toolchains: `leanprover/lean4:v4.35.0-rc3`.
- Artifact: `13387190082`, `hbl-mathlib-source-reuse-index`.
- Downloaded ZIP SHA256: `697f3c92343c5db455b6b39172dbe17335711af4ceb7d49d4b2d88e039d2c98c`.
- ZIP SHA256 and the two internal payload hashes were independently checked after download.

| Selected source tree | Lean source files | Explicit source declarations |
|---|---:|---:|
| HBL/HBL | 1106 | 4160 |
| Pinned Mathlib/Mathlib | 8569 | 221099 |

These are lexical **source inventory counts**, including definitions and private helpers. They are NOT verified-theorem counts. Generated declarations are not included. The inventory does not cover every historical HBL branch. Source header previews are not complete elaborated types. Direct-import closure is not theorem-dependency closure. Each candidate must be checked against the full original source and then compiled in its actual consumer.

The archive contains index.jsonl, a version/count summary, source SHA256 values, direct imports, line-numbered declaration candidates and public source bytes. No private repository source was uploaded to this public repository or artifact.

## Current HBL target: adjusted exterior source envelope

Do not rederive the speed-profile calculus from scratch. Inspect and reuse:

1. `HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedSpeed.lean`: `actual_Hartree_moment_locked_speed_profiles_uniform_close`, with the true moment-locked scale direction.
2. `HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedProjectionAsymptotics.lean`: `bubble_two_speed_tail` and its existing private actual-profile tail proof. A public wrapper can reuse the exact argument if needed; changed sources must be freshly replayed.
3. `HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedCoupledInverseBound.lean`: `actual_Hartree_moment_locked_coupled_inverse_bound_region`.
4. `HBL/TypeIIDynamicSelection/ActualHartreeGeneralSourceCorrection.lean`: the original-source complete-obstruction estimate already assembled inside `actual_Hartree_general_source_correction_region`.
5. `HBL/TypeIIDynamicSelection/ActualHartreeMatchedExteriorTail.lean`: `actual_Hartree_matched_exterior_core_feedback` is the consumer requiring the corrected source envelope, not only an adjusted inner norm.

The intended, still-unaccepted bridge is

`Q_adj <= Q0 + C*a*B*(abs(delta_b)+abs(delta_omega))`,

followed by the already proved full compatibility inverse and the same-source obstruction estimate. Every occurrence must use the SAME basis, physical source, selected speeds and fixed Fredholm inverse. This register supplies no new proof of the bridge and does not change 11/13.

## Moving-parameter candidates already present in HBL

- `KummerSourceTangents/ActualCompactTangentFamily.lean`: `exists_actual_compact_kummer_source_tangent_family` includes analytic parameter dependence, source tangents and residual bounds.
- `KummerParameterInverse/PhysicalParameterDerivatives.lean`: `kummer_physical_parameter_derivatives` handles real physical parameters and complex inverse operators.
- `KummerOriginGreen/FrobeniusParameterJets.lean`: `originFrobeniusCoefficientVector_contDiff` and `compact_originFrobenius_all_parameter_jets_bounded` concern origin coefficient jets.
- `TypeIIDynamicSelection/ActualOneLayerParameterTangents.lean`: `actual_phased_moving_monopole_two_parameter_tangent` retains the actual moving-cutoff derivative, including at c=0.

**Critical scope check:** the compact source-tangent family uses a fixed local annulus and `LocalKummerPair`. The current matched problem uses `OriginKummerPair` and a moving lower interface L/a. These are not interchangeable. Prove the identification and uniformity before claiming the current moving-origin problem is closed.

## Pinned Mathlib producers to search before new elementary proofs

- `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`: root-level `integral_zpow` and `integral_rpow`; do not guess their namespace.
- `Mathlib/Analysis/Calculus/ParametricIntegral.lean`: `hasFDerivAt_integral_of_dominated_of_fderiv_le` and `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
- `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`: interval versions of differentiation under the integral; moving endpoints still require their boundary terms.
- `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`: endpoint FTC and interval derivatives.
- `Lp.norm_le_mul_norm_of_ae_le_mul` for passing pointwise majorants to the actual Lp norm.

## External search routes and applicability filters

Use Mathlib's official docs, Loogle for types, LeanSearch for natural-language premises, and public project code such as `fpvandoorn/carleson` and `roos-j/lean-spherical`. Search engines may index a different Mathlib revision; verify every name and type against the pin above.

A concrete inspected external candidate is `roos-j/lean-spherical` at `f0dde64dcef87118c1d1dc9253e039da8f3f0482`, `LeanSpherical/Auto/HardyLittlewoodSobolev.lean`. Its displayed theorem concerns the LINE, with 0 < lambda < 1 and the symmetric exponent 2/(2-lambda). It is not the three-dimensional Riesz estimate used by HBL. Do not replace a 3D literature interface with this theorem without an actual dimensional argument. External licenses and full dependency locks must also be retained.

## Build discipline

Search the selected branch/commit before writing. Classify a hit as direct reuse, interface adaptation, proof-pattern only, or irrelevant. Use a minimal consumer importing the relevant modules. Reuse dependency objects only with the exact compiler, dependency pin and source/object evidence. Freshly compile changed targets, inspect complete types, and audit recursive axioms. Keep a failed-query and failed-adaptation note to avoid repeating the same search. The source inventory is a retrieval aid, never acceptance evidence.

Manuscript acceptance remains **11/13**. This round accepts no new manuscript environment and makes no claim to a complete PDE residual step or dynamical type-II rate selection.
