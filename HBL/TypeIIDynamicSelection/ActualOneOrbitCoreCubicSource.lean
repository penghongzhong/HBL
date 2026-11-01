import HBL.TypeIIDynamicSelection.ActualOneOrbitFullPotentialCore
import HBL.TypeIIDynamicSelection.ActualOneOrbitMovingMonopoleMixed
import HBL.MonopoleRadialBound
import Mathlib.Tactic

/-!
# Actual first-layer Hartree forcing: full physical quartic core potential

The original radial PDE contains the nonlocal product
  [(K * (|V_c+Z|^4-|V_c|^4)) - c_ell] V_c^3,
not merely the isolated quartic density or its potential.

The terminal one-orbit physical source is the entire actual radial
quartic interaction including all cross terms; the amplitude c_ell
is fixed by the genuine 3D inverse-square whole-radiation moment.
Strictly verified Riesz core bounds and the actual Fredholm-built
monopole radial profile yield a quantitative estimate of this
*real Hartree PDE forcing term*, retaining its true cubic multiplier.

The terminal source estimate does NOT establish the full nonterminal
two-channel projected PDE forcing, modulation slow mode, Kummer/remote
source matching or original 2.12 positive gain for every generated term.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual complex-valued Hartree source remaining after the
full physical quartic self+mixed potential has its moment-selected
constant part cancelled, multiplied by the TRUE cubic V_c³ factor. -/
def actualOneOrbitFullHartreeCoreCubicDefect (ell r : ℝ) : ℂ :=
  (((radialHartreePotential
     (actualOneOrbitFullInteractionDensity ell) r -
        actualOneOrbitMonopoleCoefficient ell : ℝ) : ℂ)) *
       (actualOneOrbitMovingMonopole ell r : ℂ) ^ 3

/-- The genuine nonlocal Hartree PDE first-layer cubic source
inherits the proved Riesz self and mixed physical centre gain.
This does not postulate a source-mass match: c_ell is fixed by
the actual 3D terminal radiation moment. -/
theorem actual_one_orbit_full_Hartree_core_cubic_source_gain
    (ell r : ℝ)
    (hell : 0 < ell) (hsmall : ell ≤ 1)
    (hr : 0 < r) (hsep : 2 * r ≤ 1 / (4 * ell))
    (hc : |actualOneOrbitMonopoleCoefficient ell| ≤ 1) :
    ‖actualOneOrbitFullHartreeCoreCubicDefect ell r‖ ≤
      (16 * r ^ 2 * ell ^ 2 * actualOneOrbitMonopoleCoefficient ell +
        (64 * Real.pi * hartreeKappa *
           actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          r ^ 2 * ell ^ 3 * Real.sqrt ell +
        (4 * Real.pi * hartreeKappa *
           actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          ell * Real.sqrt ell) *
        (1 + monopoleRadialBoundConstant) ^ 3 := by
  let B : ℝ :=
      16 * r ^ 2 * ell ^ 2 * actualOneOrbitMonopoleCoefficient ell +
        (64 * Real.pi * hartreeKappa *
           actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          r ^ 2 * ell ^ 3 * Real.sqrt ell +
        (4 * Real.pi * hartreeKappa *
           actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          ell * Real.sqrt ell
  have hPotential :
      |radialHartreePotential (actualOneOrbitFullInteractionDensity ell) r -
        actualOneOrbitMonopoleCoefficient ell| ≤ B := by
    simpa only [B] using
      actual_one_orbit_full_Hartree_core_residual_gain
        ell r hell hsmall hr hsep
  have hB : 0 ≤ B :=
    le_trans (abs_nonneg _) hPotential
  have hV :
      |actualOneOrbitMovingMonopole ell r| ≤
        1 + monopoleRadialBoundConstant := by
    dsimp [actualOneOrbitMovingMonopole]
    exact monopolePerturbedRadialProfile_abs_le
      (R := monopoleQuadraticRadius (actualOneOrbitMonopoleCoefficient ell))
      hr hc
  have hVpow :
      |actualOneOrbitMovingMonopole ell r| ^ 3 ≤
        (1 + monopoleRadialBoundConstant) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hV 3
  have hTerm :
      ‖actualOneOrbitFullHartreeCoreCubicDefect ell r‖ =
        |radialHartreePotential (actualOneOrbitFullInteractionDensity ell) r -
            actualOneOrbitMonopoleCoefficient ell| *
          |actualOneOrbitMovingMonopole ell r| ^ 3 := by
    unfold actualOneOrbitFullHartreeCoreCubicDefect
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
  rw [hTerm]
  change
    |radialHartreePotential (actualOneOrbitFullInteractionDensity ell) r -
        actualOneOrbitMonopoleCoefficient ell| *
      |actualOneOrbitMovingMonopole ell r| ^ 3 ≤
        B * (1 + monopoleRadialBoundConstant) ^ 3
  exact mul_le_mul hPotential hVpow (pow_nonneg (abs_nonneg _) 3) hB

end HBL.TypeIIDynamicSelection
