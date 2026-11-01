import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalRadiation
import Mathlib.Tactic

/-!
# Physical linear mixed Hartree charge of the selected terminal orbit

The genuine full-radiation quartic density has a real-linear Hartree
component 4 W(r)^3 Re Z_ell(r). The selected smooth nonzero annular
terminal datum is exactly zero near the origin, so its critical rescaling
is supported at physical radii comparable to ell^(-1).

We derive the pointwise O(ell^(7/2)) bound directly from the actual
stationary 3D bubble and actual complex critical rescaling, with NO
assumed blowup rate and NO abstract source-order marker.

This is a first source estimate for the original one-layer proposition,
not the full nonlinear three-region source cancellation.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The fixed smooth annular terminal profile takes values in [0,1]. -/
theorem actual_one_orbit_terminal_bump_unit_bound (r : ℝ) :
    0 ≤ actualOneOrbitTerminalBump r ∧
      actualOneOrbitTerminalBump r ≤ 1 := by
  have ha0 : 0 ≤ cutoff (4 * r) := by
    change 0 ≤ Real.smoothTransition (4 * r - 1)
    exact Real.smoothTransition.nonneg _
  have ha1 : cutoff (4 * r) ≤ 1 := by
    change Real.smoothTransition (4 * r - 1) ≤ 1
    exact Real.smoothTransition.le_one _
  have hb0 : 0 ≤ cutoff (r / 2) := by
    change 0 ≤ Real.smoothTransition (r / 2 - 1)
    exact Real.smoothTransition.nonneg _
  have hb1 : cutoff (r / 2) ≤ 1 := by
    change Real.smoothTransition (r / 2 - 1) ≤ 1
    exact Real.smoothTransition.le_one _
  unfold actualOneOrbitTerminalBump
  constructor
  · exact mul_nonneg ha0 (by linarith)
  · calc
      cutoff (4 * r) * (1 - cutoff (r / 2)) ≤
          1 * (1 - cutoff (r / 2)) :=
        mul_le_mul_of_nonneg_right ha1 (by linarith)
      _ ≤ 1 := by linarith

/-- The actual rescaled radiation is identically zero on the inner
physical core 0 < r ≤ (4 ell)^(-1). -/
theorem actual_one_orbit_rescaled_terminal_zero_core
    (ell r : ℝ) (hell : 0 < ell)
    (hr : r ≤ 1 / (4 * ell)) :
    rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r = 0 := by
  have hcoef : 0 < 4 * ell := by positivity
  have hscaled : ell * r ≤ 1 / 4 := by
    have h := (le_div_iff₀ hcoef).mp hr
    nlinarith
  have hz := actual_one_orbit_terminal_bump_zero_core hscaled
  simp [rescalePhysicalRadiation, actualOneOrbitTerminalRadiation, hz]

/-- The same rescaled terminal radiation vanishes beyond 4/ell. -/
theorem actual_one_orbit_rescaled_terminal_zero_far
    (ell r : ℝ) (hell : 0 < ell)
    (hr : 4 / ell ≤ r) :
    rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r = 0 := by
  have hscaled : 4 ≤ ell * r := by
    have h := (div_le_iff₀ hell).mp hr
    nlinarith
  have hz := actual_one_orbit_terminal_bump_zero_far hscaled
  simp [rescalePhysicalRadiation, actualOneOrbitTerminalRadiation, hz]

/-- The real three-dimensional stationary bubble W=(1+r²)^(-1/2)
decays at least like r^(-1) at every strictly positive radius. -/
theorem actual_one_orbit_bubble_le_inverse_radius
    (r : ℝ) (hr : 0 < r) :
    bubble r ≤ 1 / r := by
  have hroot :
      r ≤ Real.sqrt (1 + r ^ 2) := by
    calc
      r = Real.sqrt (r ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hr]
      _ ≤ Real.sqrt (1 + r ^ 2) :=
        Real.sqrt_le_sqrt (by linarith : r ^ 2 ≤ 1 + r ^ 2)
  have hrootpos : 0 < Real.sqrt (1 + r ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  unfold bubble
  have hinv : 1 / Real.sqrt (1 + r ^ 2) ≤ 1 / r :=
    (div_le_div_iff₀ hrootpos hr).2 (by simpa using hroot)
  simpa only [one_div] using hinv

/-- The REAL-LINEAR component 4 W³ Re Z of the exact quartic Hartree
density vanishes in the inner core and is uniformly O(ell^(7/2))
everywhere on the positive half-line. No time-decay exponent is imposed:
ell>0 is arbitrary and is later selected by the true Hartree dynamics. -/
theorem actual_one_orbit_terminal_mixed_linear_density_seven_halves_gain
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r) :
    |4 * bubble r ^ 3 *
        (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re| ≤
      256 * ell ^ 3 * Real.sqrt ell := by
  by_cases hcore : ell * r ≤ 1 / 4
  · have hcut : r ≤ 1 / (4 * ell) := by
      have hcoef : 0 < 4 * ell := by positivity
      apply (le_div_iff₀ hcoef).2
      nlinarith [hcore]
    rw [actual_one_orbit_rescaled_terminal_zero_core ell r hell hcut]
    simp only [Complex.zero_re, mul_zero, abs_zero]
    positivity
  · have hfar : 1 / 4 < ell * r := lt_of_not_ge hcore
    have hR : 1 / r ≤ 4 * ell := by
      apply (div_le_iff₀ hr).2
      nlinarith [hfar]
    have hb : 0 ≤ bubble r := by
      unfold bubble
      positivity
    have hW : bubble r ≤ 4 * ell :=
      (actual_one_orbit_bubble_le_inverse_radius r hr).trans hR
    have hPow : bubble r ^ 3 ≤ (4 * ell) ^ 3 :=
      pow_le_pow_left₀ hb hW 3
    have hReal :
      (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re =
        Real.sqrt ell * actualOneOrbitTerminalBump (ell * r) := by
      unfold rescalePhysicalRadiation actualOneOrbitTerminalRadiation
      simp
    have hBump := actual_one_orbit_terminal_bump_unit_bound (ell * r)
    have hZ :
      |(rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re|
        ≤ Real.sqrt ell := by
      rw [hReal, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg hBump.1]
      calc
        Real.sqrt ell * actualOneOrbitTerminalBump (ell * r) ≤
          Real.sqrt ell * 1 :=
            mul_le_mul_of_nonneg_left hBump.2 (Real.sqrt_nonneg _)
        _ = _ := by ring
    have hWnonneg : 0 ≤ 4 * bubble r ^ 3 := by positivity
    calc
      |4 * bubble r ^ 3 *
          (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re|
        = 4 * bubble r ^ 3 *
            |(rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re| := by
          rw [abs_mul, abs_of_nonneg hWnonneg]
      _ ≤ 4 * (4 * ell) ^ 3 *
            |(rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hPow (by norm_num))
            (abs_nonneg _)
      _ ≤ 4 * (4 * ell) ^ 3 * Real.sqrt ell := by
          exact mul_le_mul_of_nonneg_left hZ (by positivity)
      _ = 256 * ell ^ 3 * Real.sqrt ell := by ring

end HBL.TypeIIDynamicSelection
