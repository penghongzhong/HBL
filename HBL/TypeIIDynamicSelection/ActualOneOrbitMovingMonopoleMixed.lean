import HBL.TypeIIDynamicSelection.ActualOneOrbitLinearMixedCenter
import HBL.TypeIIDynamicSelection.ActualRadiation3DMoment
import HBL.MonopoleMovingCutoffDerivative
import HBL.MonopoleRadialBound
import Mathlib.Tactic

/-!
# Physical mixed Hartree source on the ACTUAL moment-dependent monopole background

The manuscript's actual profile is V_c = W + c (1-chi(|c|r/4)) Phi_mon,
with c= kappa_H ell m0[g], not W alone. The selected nonzero annular
regular radiation has Z_ell=sqrt(ell)g(ell r).

This module identifies c with the exact full-radiation Hartree centre
and proves the real-linear quartic density 4 V_c³ Re Z_ell has
pointwise order ell^(7/2) with an explicit fixed constant.

No final blowup exponent, abstract source inverse, or a prescribed
Hartree residual cancellation is assumed. The full manuscript 2.12
two-threshold/Kummer/remote matching is NOT claimed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

/-- The *physical* monopole strength of this chosen terminal radiation. -/
def actualOneOrbitMonopoleCoefficient (ell : ℝ) : ℝ :=
  hartreeKappa * ell *
    actualPhysicalInverseSquareMoment actualOneOrbitTerminalRadiation

/-- Exactly the original moving Hartree monopole profile, not a free
or local-cubic replacement. -/
def actualOneOrbitMovingMonopole (ell r : ℝ) : ℝ :=
  let c := actualOneOrbitMonopoleCoefficient ell
  monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r

/-- The genuine real-linear part of the full mixed quartic density
at the moment-generated monopole background. -/
def actualOneOrbitMovingMixedLinear (ell r : ℝ) : ℝ :=
  4 * actualOneOrbitMovingMonopole ell r ^ 3 *
    (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re

/-- Identifies our coefficient with the unique genuine slow monopole
source of the *entire* rescaled physical terminal radiation. -/
theorem actual_one_orbit_monopole_coefficient_eq_full_radiation_center
    (ell : ℝ) (hell : 0 < ell) :
    actualOneOrbitMonopoleCoefficient ell =
      actualRadiationCenter
        (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation) := by
  symm
  exact actual_whole_radiation_center_eq_physical_threeD_moment
    ell hell actualOneOrbitTerminalRadiation

/-- A finite positive envelope depending only on the fixed selected
terminal datum and the previously constructed radial monopole. -/
def actualOneOrbitMovingEnvelope : ℝ :=
  4 + hartreeKappa *
    actualPhysicalInverseSquareMoment actualOneOrbitTerminalRadiation *
      monopoleRadialBoundConstant

theorem actual_one_orbit_moving_envelope_pos :
    0 < actualOneOrbitMovingEnvelope := by
  have hm := actual_one_orbit_terminal_radiation_positive_moment
  have hM := monopoleRadialBoundConstant_pos
  unfold actualOneOrbitMovingEnvelope hartreeKappa
  positivity

/-- The full moment-corrected monopole has physical size O(ell)
on the genuine support of the rescaled chosen radiation. -/
theorem actual_one_orbit_moving_monopole_size_on_radiation_support
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (hremote : 1 / 4 < ell * r) :
    |actualOneOrbitMovingMonopole ell r| ≤
      actualOneOrbitMovingEnvelope * ell := by
  let c := actualOneOrbitMonopoleCoefficient ell
  have hcpos : 0 ≤ c := by
    dsimp [c, actualOneOrbitMonopoleCoefficient]
    have hm := actual_one_orbit_terminal_radiation_positive_moment
    unfold hartreeKappa
    positivity
  have hbr : 0 ≤ bubble r := by
    unfold bubble
    positivity
  have hW : bubble r ≤ 4 * ell := by
    have hRecip : 1 / r ≤ 4 * ell := by
      apply (div_le_iff₀ hr).2
      nlinarith [hremote]
    exact (actual_one_orbit_bubble_le_inverse_radius r hr).trans hRecip
  let χ : ℝ := cutoff (|c| * r / 4)
  have hχ0 : 0 ≤ χ := by
    dsimp [χ]
    change 0 ≤ Real.smoothTransition (|c| * r / 4 - 1)
    exact Real.smoothTransition.nonneg _
  have hχ1 : χ ≤ 1 := by
    dsimp [χ]
    change Real.smoothTransition (|c| * r / 4 - 1) ≤ 1
    exact Real.smoothTransition.le_one _
  have hCut : |1 - χ| ≤ 1 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - χ)]
    linarith
  have hM := monopoleRadialProfile_abs_le (r := r) hr
  have hprod : |c * (1 - χ) * monopoleRadialProfile r| ≤
      |c| * monopoleRadialBoundConstant := by
    rw [abs_mul, abs_mul]
    have hcm :
        |1 - χ| * |monopoleRadialProfile r| ≤
          monopoleRadialBoundConstant := by
      calc
        _ ≤ 1 * |monopoleRadialProfile r| :=
          mul_le_mul_of_nonneg_right hCut (abs_nonneg _)
        _ ≤ monopoleRadialBoundConstant := by simpa using hM
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left hcm (abs_nonneg c))
  have hprofile :
      |actualOneOrbitMovingMonopole ell r| ≤
        bubble r + |c| * monopoleRadialBoundConstant := by
    dsimp [actualOneOrbitMovingMonopole]
    rw [monopoleMovingCutoffProfile_eq]
    change |bubble r + c * (1 - χ) * monopoleRadialProfile r| ≤ _
    exact (abs_add_le _ _).trans
      (add_le_add (le_of_eq (abs_of_nonneg hbr)) hprod)
  calc
    _ ≤ bubble r + |c| * monopoleRadialBoundConstant := hprofile
    _ ≤ 4 * ell + c * monopoleRadialBoundConstant := by
      rw [abs_of_nonneg hcpos]
      exact add_le_add_left hW _
    _ = actualOneOrbitMovingEnvelope * ell := by
      dsimp [actualOneOrbitMovingEnvelope, c, actualOneOrbitMonopoleCoefficient]
      ring

/-- The actual rescaled real terminal datum stays below sqrt(ell).
This reuses the fixed nonnegative cutoff rather than postulating
a radiation decay rate in renormalized time. -/
theorem actual_one_orbit_rescaled_terminal_real_bound
    (ell r : ℝ) :
    |(rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re|
      ≤ Real.sqrt ell := by
  have hreal :
      (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re =
        Real.sqrt ell * actualOneOrbitTerminalBump (ell * r) := by
    unfold rescalePhysicalRadiation actualOneOrbitTerminalRadiation
    simp
  have hB := actual_one_orbit_terminal_bump_unit_bound (ell * r)
  rw [hreal, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg hB.1]
  calc
    Real.sqrt ell * actualOneOrbitTerminalBump (ell * r) ≤
      Real.sqrt ell * 1 :=
        mul_le_mul_of_nonneg_left hB.2 (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- REAL physical nonlinear mixed-density source at V_c, rather than W:
the gain O(ell^(7/2)) survives with the genuinely selected monopole c.
No off-terminal support or selected-rate assumption is inserted. -/
theorem actual_one_orbit_moving_monopole_mixed_linear_seven_halves_gain
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r) :
    |actualOneOrbitMovingMixedLinear ell r| ≤
      4 * actualOneOrbitMovingEnvelope ^ 3 *
        ell ^ 3 * Real.sqrt ell := by
  by_cases hcore : ell * r ≤ 1 / 4
  · have hcoef : 0 < 4 * ell := by positivity
    have hcut : r ≤ 1 / (4 * ell) := by
      apply (le_div_iff₀ hcoef).2
      nlinarith [hcore]
    have hz := actual_one_orbit_rescaled_terminal_zero_core
      ell r hell hcut
    simp [actualOneOrbitMovingMixedLinear, hz]
    have hC := actual_one_orbit_moving_envelope_pos
    positivity
  · have hremote : 1 / 4 < ell * r := lt_of_not_ge hcore
    have hV := actual_one_orbit_moving_monopole_size_on_radiation_support
      ell r hell hr hremote
    have hVcube :
        |actualOneOrbitMovingMonopole ell r| ^ 3 ≤
          (actualOneOrbitMovingEnvelope * ell) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) hV 3
    have hZ := actual_one_orbit_rescaled_terminal_real_bound ell r
    have habs :
        |actualOneOrbitMovingMixedLinear ell r| =
          4 * |actualOneOrbitMovingMonopole ell r| ^ 3 *
            |(rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re| := by
      unfold actualOneOrbitMovingMixedLinear
      rw [abs_mul, abs_mul, abs_pow]
      norm_num
    rw [habs]
    calc
      _ ≤ 4 * |actualOneOrbitMovingMonopole ell r| ^ 3 *
          Real.sqrt ell :=
        mul_le_mul_of_nonneg_left hZ (by positivity)
      _ ≤ 4 * (actualOneOrbitMovingEnvelope * ell) ^ 3 *
          Real.sqrt ell :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hVcube (by norm_num))
          (Real.sqrt_nonneg ell)
      _ = _ := by ring

end HBL.TypeIIDynamicSelection
