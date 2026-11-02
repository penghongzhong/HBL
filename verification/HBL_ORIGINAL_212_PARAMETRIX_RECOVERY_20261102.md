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


## Crucial reverse-dependency reduction: one orbit, not uniform terminal-data theory

The private reconciled main target `thm:main` is **existential**:
one actual radial strong Hartree Type-II solution with the terminal
radiation and the dynamical concentration rate *selected from its own
modulation PDE*. It does **not** assert Type-II blowup for every datum
in an open Sobolev ball, nor a codimension-one C1 data manifold.

Therefore choose ONCE a nonzero real radial
`g in C_c^infty({1/4<|x|<4})` with positive genuine quartic Hartree
moment, scale its amplitude into the cited high-regularity LWP ball,
and construct only the physical trajectory `z_g(t)`. All physical
offterminal weighted estimates and moments need be proved for this
single concrete `g`; uniform `(h,g)` source estimates and local
Lipschitz dependence across a small data ball can be deleted from
the core 2.12--2.14 chain if they are not used by the existence
and modulation selection proof. Keep exactly the `D_zeta Theta`
parameter derivatives needed for the finite-dimensional
shooting/invertibility of the *real rate-selecting* dynamics.

This is a mathematical shortening of the PAPER's original 2.13,
not a deletion of a proof obligation or a numerical denominator
manipulation. Do not count the original environment until the
revised entire statement and exact Lean theorem type are accepted.
The final Type-II exponent remains a PDE output, NEVER a hypothesis.

## Prefer physical moment cutoff over an arbitrary moving radius

The original Hartree radial monopole cutoff is
`eta_c(s,r)=1-cutoff(c(s)r/4)`, where
`c(s)=kappa_H ell(s) m_0[z_g(t(s))]` is the **actual whole-radiation
quartic Hartree moment**. For positive c, this is precisely the
parametrix cutoff with `R(s)=4/c(s)`; c=0 is handled by the original
form without dividing by c. The strictly accepted PDE moment identity
gives

```math
c_s=-b c+\kappa_{\rm H}\ell^3 m_0'(t),\qquad
\frac{R_s}{R}-b=-\ell^2\frac{m_0'(t)}{m_0(t)}.
```

Thus the exact local material-cutoff commutator has a true physical
`ell^2` factor, rather than an independent `|R_s|/R+|b|` bound.
It is already strictly supported by
`ActualMomentCutoffTransport.lean` plus
`ActualCutoffUniformTransport.lean` (the moment derivative is derived
from the actual radial Hartree PDE under visible dominated-flow inputs).

The SHORT route for the next weight lemma is: reuse this exact
transport bound; derive `r/R in [1,2]` only on the true shell;
bound the first/second spatial cutoff commutators by actual
`R^{-1}` and `R^{-2}`; absorb the nonlocal exterior center into the
forced monopole charge; control the rest with the already proved
actual complex moving-remote Riesz `O(r^2/R^2)` remainder and a
genuine physical moment/source estimate. DO NOT treat the whole
cutoff nonlinear commutator as local or vanishing.

If `ell(s) <= C s^{-beta_-}`, `beta_->1/2`, and the actual
relative moment flux is bounded (both from the selected Hartree
trajectory), then `ell^2` gives **derived** time exponent
`2beta_->1`, i.e. the original positive `2beta_--1` gain.
This `beta_-` is a trap-window lower bound, not the selected
asymptotic Type-II exponent.


## Minimal *mathematically meaningful* revision of original 2.12, if necessary

The original lemma claims the complete regional correction is
`unique` while simultaneously presupposing independently normalized
Kummer and remote inverses and two-sided interface matching. That
combination is not automatic; the accepted Wronskian obstruction shows
why arbitrary Cauchy gluing fails.

For the EXISTENTIAL `thm:main`, full uniqueness among all global
profiles is unnecessary. Keep uniqueness of the two real threshold
charges and uniqueness **within a fixed prescribed regional inverse,
canonical cutoff and normalization**, but otherwise state existence of
one canonical localized parametrix correction. Replace an unjustified
exact global matching assertion by the proved PDE identity plus
quantitatively higher-order cutoff/whole-Hartree source residuals.
This does NOT weaken the essential one-layer conclusion:
`Pi_rho R(V+Delta)=P_rho(zeta) zeta_s`
and all new actual source atoms have strictly positive
`kappa_prof` weight gain. Those two remain HARD proof obligations.

Do not modify the private manuscript theorem label or count this as
accepted until the exact source-level parametrix and all positive
gain estimates are strictly compiled and compared line by line.


## 2026-11-02 — Exact norm-improvement replacement target for original 2.12

The shortest *meaningful* potential replacement for the existing
`Pi_rho`/all-atoms statement is the STRONGER actual Hartree PDE
weighted **residual inequality**, with the parameter tangent
retained:

```math
\|\mathcal F(V_{<\rho}+\Delta V_{\rho})
     -\mathcal P_{\rho}(\zeta)\zeta_s\|_{X_f^{\rm sc}}
  \le C_\rho s^{-\rho-\kappa_{\rm prof}},
\qquad \kappa_{\rm prof}>0 .
```

This avoids introducing source-order labels by hand, and implies
the absence of residual terms at order rho once the actual
finite dynamic-atom expansion is shown to exist. It requires
constructing ONE canonical localized correction (not arbitrarily
altering both normalized Kummer Wronskian boundary conditions),
plus verifying the original source and cutoff commutator estimates
on the actual full one-orbit physical flow. The norm must be the
ACTUAL manuscript space X_f^sc (or an explicitly proved embedding
from a stronger norm), never a scalar surrogate.

**Two sharply distinguished physical cutoffs:**
- Actual SLOW MONOPOLE `1-cutoff(c(s)r/4)`:
  `c(s)=kappa_H*ell(s)*m_0(t(s))`.
  Its material transport has the exact derived
  `ell(s)^2 * |m_0'(t(s))|/m_0(t(s))` coefficient, giving
  `s^{-1-(2beta_--1)}` after the true scale trap.
- Actual THREE-REGION OVERLAP `1-cutoff(r/R(s))`: its
  spatial derivative costs `R^-1,R^-2` and its material
  derivative contains `R_s/R-b`. The source/derivative
  asymptotics of the actual normalized H+/H-, Kummer, remote
  corrections on the MOVING overlap must be proved before
  asserting any `rho_*>0` gain. Local Kummer inversion on a
  fixed annulus, even if strict Lean checked, does not by itself
  imply the required moving-overlap uniform estimates.

**New precisely scoped physical attempts** (count NOTHING before terminal strict CI):
- 41381828235: genuine physical Hartree PDE cutoff exponent
  `2beta_--1` in
  `ActualPDEMomentCutoffStrictGain.lean`; compilation and
  all three kernel declaration checks succeeded but
  `-DwarningAsError` found one *unused binder* `hC`.
  Corrected strict rerun 41383533549.
- 41382215159: bounded actual terminal relative moment
  `|m_0'|/m_0` derived from positivity and continuity
  (rather than a separate bounded-flux assumption) in
  `ActualHartreeMomentFluxFromContinuity.lean`.
- 41382868776 (replaced by 41383538450):
  uniform ALL-R / EVENTUAL ALL-S actual physical orbit
  cutoff `s^{-1-(2beta_--1)}`, formed by combining the
  actual Hartree PDE-moment identity and terminal continuity.
- 41383441468: the second, independent smooth radial
  overlap cutoff's true global C2 bound and `R^-1,R^-2`
  geometric factors, in `ActualOneLayerSpatialOverlapGain.lean`.

All four attempts include independent source, theorem `#check`,
`#print axioms`, pinned Lean 4.35.0-rc3/Mathlib
a98628e16c11f5167f16124105ddce53efa9bfe5.
They do not claim to prove the original complete 2.12.

**Remaining acceptance-blocking PDE estimates, regardless of build count:**
(A) one actual offterminal radiation's complete weighted
  Hartree residual at the current minimal weight in X_f^sc;
(B) uniform actual normalized Kummer source-to-jet bounds
  on MOVING physical overlaps plus remote-block analytic
  coefficient/derivative estimates, not just fixed compact annuli;
(C) the entire nonlinear Riesz whole/inner/remote
  commutator under the same partition, with a genuine higher-order
  norm bound after the forced monopole moment is removed;
(D) multi-source parameter and Frobenius terms, proving the same
  positive `kappa_prof` uniformly and preserving a canonical
  normalization. Only then is the new full original theorem eligible
  for 10/13.
