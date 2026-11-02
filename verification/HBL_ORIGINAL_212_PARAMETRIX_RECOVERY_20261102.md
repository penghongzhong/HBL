# HBL original 2.12 — structural blocker audit and lean proof recovery (2026-11-02)

## Numerator and precise target

- Retained original paper: **9/13**; historical original environment: **9/21**. The original manuscript `prop:one-layer-stage3` is **OPEN**. Do not increment the original numerator for auxiliary CI successes.
- Other original open items: 2.13 (`thm:finite-profile-stage3`), 2.14 (`prop:global-H1-profile-v3`), and the genuine Type-II dynamical-rate main theorem.
- Actual 2.12 states: For the minimum unresolved physical atom weight `rho`, construct a UNIQUE normalized correction consisting of *actual* H+/H−, Kummer, and remote pieces, plus two real forced affine charges, such that the full original Hartree PDE residual at exactly weight `rho` is removed except for the parameter-velocity tangent; **every generated term from this very correction** has order at least `rho+kappa_prof` with `kappa_prof>0` from the physics.
- A valid original theorem MUST make its `GeneratedTerm` fields consequences of the true nonlinear PDE expansion rather than assign a `cause` and `extra_nonneg` by construction. The old `OneLayerElimination.lean`/ `FiniteProfile.lean` demonstrate conditional algebraic bookkeeping only.

## Why repeated 3500–4100-job SUCCESS did not raise 9/13

1. Each full `lake build` rebuilds/replays thousands of Mathlib, HBL and imported modules. The CI success means these **listed Lean theorem statements** were proved, not that the full private TeX manuscript claim is proved.
2. In `HBL/OneLayerElimination.lean`, `ThresholdSolver`/ `RegionalSolver` and `GeneratedTerm` are arbitrary typed inputs. `oneMinimalWeightCluster_eliminated` does not instantiate the actual Hartree regional inverse/source/weight hierarchy. `HBL/FiniteProfile.lean` supplies the uniform weight-step and physical region bounds as hypotheses. Neither is a proof of original 2.12/2.13.
3. `HBL/RegularRadiationOriginalEnvironment.lean` retains `CitedHighRegularityHartreeLocalTheory` as an explicit **external literature interface**. The passage from Sobolev/distributional flow to a pointwise radial C2 field and the uniform spatial/temporal weighted estimates across the actual moving cutoff remain distinct obligations.
4. **Actual theorem-level obstruction:** Strict CI [41371554435](https://github.com/penghongzhong/HBL/actions/runs/41371554435) proved the actual Kummer normalized left/right Wronskian conditions force *both* complex homogeneous correction coefficients to be zero. Strict CI [41371435512](https://github.com/penghongzhong/HBL/actions/runs/41371435512) proved inner Cauchy data uniquely determine these coefficients and outer C1 matching requires a nontrivial transfer equation. Therefore `add homogeneous corrections to match inner jets` does **not** preserve the original normalized Kummer inverse. Repeating that local Cauchy construction does not close 2.12.
5. Exact source equality in all three regions does not automatically imply a globally glued, smooth, decaying solution or a strictly higher-order nonlinear remainder.

## What is newly, really solved

- Physical Hartree PDE -> genuine dynamical-phase renormalized radiation equation (no assumed rate): strict SUCCESS [41371904800](https://github.com/penghongzhong/HBL/actions/runs/41371904800).
- Same physical PDE -> exact full core/radiation Riesz interaction source without `hRadiationPDE` among the inputs: strict SUCCESS [41371909104](https://github.com/penghongzhong/HBL/actions/runs/41371909104).
- The real nonterminal Hartree flow's actual spacetime C1 scale/clock, radial Laplacian and complex phase covariance: previously independently strict SUCCESS.
- True whole-to-remote moment mismatch, complex nonlocal remote Riesz potential, genuine Kummer local inverse and two H+/- weighted solutions: independently strictly checked.
- Real classical H+/H− inner positive-radius C2 solutions: SUCCESS [41367692404](https://github.com/penghongzhong/HBL/actions/runs/41367692404).
- 31-source/flow/classical-inner same-environment replay: SUCCESS [41371783516](https://github.com/penghongzhong/HBL/actions/runs/41371783516).
- These remain **auxiliary proofs** relative to the unproved original 2.12.

## Corrected minimal mathematical construction: regional parametrix

Keep the original normalized H+/H−, Kummer, and remote inverses unchanged; do **not** use forbidden extra homogeneous freedom.

For the true smooth time-dependent overlap `chi(s,r)=1-cutoff(r/R(s))`, prove the EXACT full Hartree residual identity:

```math
\mathcal R(\chi f)-\chi\mathcal R(f)
 = i(\chi_s+b r\chi_r)f+2\chi_r f_r+
   (\chi_{rr}+2\chi_r/r)f+
   \bigl[\mathcal N(\chi f)-\chi\mathcal N(f)\bigr].
```

The real material coefficient is

```math
\chi_s+b r\chi_r
 = (r/R)(R_s/R-b)\,\mathrm{cutoff}'(r/R).
```

This is now encoded in `HBL/TypeIIDynamicSelection/ActualOneLayerMovingParametrixTransport.lean`, with its full actual nonlocal residual and genuine transition-shell bound. Its strict CI is [41378171975](https://github.com/penghongzhong/HBL/actions/runs/41378171975); do not mark it accepted before it succeeds.

The already STRICT actual physical-moment cutoff theorem `actual_Hartree_PDE_cutoff_uniform_all_r_length_gain` gives, for the moment-dependent cutoff and actual radial Hartree PDE, the **derived** transport factor

```math
|\partial_s\chi+b r\partial_r\chi|
 \le 2 C_\chi\,\ell(s)^2\,
     |\mathfrak m_0'(t(s))|/\mathfrak m_0(t(s))
```

with no imposed final Type-II blowup exponent. This is more useful than independently bounding `chi_s` and `b r chi_r`. Under the modulation trapping range `ell(s) \lesssim s^{-beta_-}` with `beta_->1/2` and a **proved** physical normalized moment-flux bound, it yields the genuine new time order `1+(2beta_--1)`.

The other two local transition-shell costs are explicitly `R^{-1} f_r` and `R^{-2}f`. The nonlocal part MUST use the true complex quartic Riesz density and its whole-minus-remote center mismatch; it cannot be discarded as a local cubic. Show a positive gain for every term *after* localizing the actual C2 region corrections, using the actual Kummer/Frobenius/remote bounds.

## New short proof chain and hard acceptance gates

1. **Already accepted**: actual offterminal physical Hartree PDE -> one common complex nonlocal source, real and imaginary Fredholm channels, classical inner solution, Kummer inverse, moving remote density, dynamic phase, transport.
2. **Next real mathematical assertion, not yet accepted**: construct regionally localized corrections from the actual source and prove their GLOBAL residual equals the corrected current-weight source plus the explicitly displayed physical cutoff and nonlinear commutators. No exact two-interface C1 matching assumption is needed.
3. **Next real estimate, not yet accepted**: prove the actual localized Hartree solution's weighted global residual norm and every transition/far-field Riesz/parameter/Frobenius term has positive order, using its real physical `ell_s`, `c_s`, `R_s`, time jets, kernel integrals, and chosen cutoff windows. A bounded/unproved `GeneratedTerm` list is not sufficient.
4. **Only then** write and strictly check a Lean theorem whose entire conclusion matches private manuscript original `prop:one-layer-stage3`: correction existence and uniqueness, exact minimum-weight residual elimination, and **uniform positive gain for all new terms**.
5. With this actual theorem, prove the original 2.13 finite recursion **without** a separate `hstep` weight-growth premise; then global physical H1 2.14 and PDE-derived Type-II rate.

## CI performance discipline

- Reuse already verified exact source commits and `.lake/build` caches; compile **one new load-bearing source plus its #check/#print axioms audit** per CI, not the whole project as an acceptance proxy.
- Only claim success when `lake env lean --trust=0 -DwarningAsError=true`, declaration type and transitive axiom list all pass; no `sorry`, `admit`, added `axiom` or previously unsupported analytic assumptions.
- **Never report 10/13 solely because a module succeeded.** The manuscript original, mathematical hypothesis equality, Lean theorem type and provenance must be audited together.
