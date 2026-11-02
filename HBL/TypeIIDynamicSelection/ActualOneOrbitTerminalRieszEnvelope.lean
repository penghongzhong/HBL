import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalRadiation
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalNonlocalSharpGain
import HBL.TypeIIDynamicSelection.ActualHartreeMomentRadiusWindow
import HBL.TypeIIDynamicSelection.ActualHartreeNonlocalWeightedSource
import HBL.TypeIIDynamicSelection.ActualHartreeRieszMeasurability
import Mathlib.Tactic

/-!
# HBL 2.12: remove abstract decay inputs for the ONE selected physical datum

For the actually constructed nonzero smooth annular terminal radiation
g(r) = cutoff(4r)*(1-cutoff(r/2)), prove genuine uniform amplitude
bound |g|<=1 and true quartic Hartree Riesz-density envelope
|g|^4 <=17*bubble^2 on positive radii. These are derived from the
chosen original smooth cutoff and its exact support.

The previously strict-certified full nonlocal inverse-square Hartree
cutoff commutator can then be specialized to this concrete g, with no
hypothesized B, D or generated source order.

The selected regular Hartree flow extending g and its moving-orbit
uniform estimates are still separate necessary obligations in original
2.12. No blowup exponent is prescribed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.AffineTail HBL.Modulation.Monopole

/-- Genuine terminal radiation is pointwise bounded by one, globally. -/
theorem actual_one_orbit_terminal_radiation_norm_le_one
    (r : ℝ) : ‖actualOneOrbitTerminalRadiation r‖ ≤ 1 := by
  have hc0 : 0 ≤ cutoff (4*r) := Real.smoothTransition.nonneg _
  have hc1 : cutoff (4*r) ≤ 1 := Real.smoothTransition.le_one _
  have hq0 : 0 ≤ 1 - cutoff (r/2) := by
    have := Real.smoothTransition.le_one (r/2 - 1)
    dsimp [cutoff]
    linarith
  have hq1 : 1 - cutoff (r/2) ≤ 1 := by
    have := Real.smoothTransition.nonneg (r/2 - 1)
    dsimp [cutoff]
    linarith
  change ‖((cutoff (4*r) * (1-cutoff (r/2)) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hc0 hq0)]
  calc
    cutoff (4*r) * (1-cutoff (r/2)) ≤
        1 * (1-cutoff (r/2)) :=
      mul_le_mul_of_nonneg_right hc1 hq0
    _ ≤ 1*1 := mul_le_mul_of_nonneg_left hq1 (by norm_num)
    _ = 1 := by ring

/-- The genuine terminal quartic density has the bubble-squared Riesz
envelope: this is NOT a prescribed decay hypothesis. -/
theorem actual_one_orbit_terminal_quartic_bubble_envelope
    (r : ℝ) (hr : 0 < r) :
    ‖actualOneOrbitTerminalRadiation r‖ ^ 4 ≤ 17 * bubble r ^ 2 := by
  have hpos : 0 < 1 + r ^ 2 := by positivity
  have hBubble : bubble r ^ 2 = (1 + r ^ 2)⁻¹ := by
    unfold bubble
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  by_cases hfar : 4 ≤ r
  · have heq := actual_one_orbit_terminal_bump_zero_far hfar
    have hz : actualOneOrbitTerminalRadiation r = 0 := by
      simp [actualOneOrbitTerminalRadiation, heq]
    rw [hz]
    simp only [norm_zero, zero_pow (by norm_num : (4:ℕ) ≠ 0)]
    positivity
  · have hr4 : r < 4 := lt_of_not_ge hfar
    have hrad : r ^ 2 ≤ 16 := by
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr4.le)]
    have hOne : ‖actualOneOrbitTerminalRadiation r‖ ^ 4 ≤ 1 := by
      simpa using (pow_le_pow_left₀ (norm_nonneg _)
        (actual_one_orbit_terminal_radiation_norm_le_one r) 4)
    calc
      ‖actualOneOrbitTerminalRadiation r‖ ^ 4 ≤ 1 := hOne
      _ ≤ 17 * bubble r ^ 2 := by
        rw [hBubble, ← div_eq_mul_inv]
        exact (le_div_iff₀ hpos).2 (by nlinarith [hrad])

/-- FULL physical nonlocal Hartree commutator for this ONE real
annular terminal radiation, with all analytic quartic-envelope data
proved from the original datum itself. -/
theorem actual_one_orbit_terminal_physical_nonlocal_sharp
    (ell R r : ℝ) (hell : 0 < ell) (hR : 0 < R) (hr : 0 < r) :
    ‖complexRadialHartreeNonlinearity
        (fun x => actualOneLayerInnerOverlapCutoff R x *
          rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation x) r -
      actualOneLayerInnerOverlapCutoff R r *
        complexRadialHartreeNonlinearity
          (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation) r‖ ≤
      (34 * radialHartreeRowBoundConstant) *
        ell ^ 2 * Real.sqrt ell := by
  have hz : Measurable actualOneOrbitTerminalRadiation :=
    (Complex.continuous_ofReal.comp
      actual_one_orbit_terminal_bump_smooth.continuous).measurable
  have h := actual_Hartree_physical_nonlocal_cutoff_sharp_length_gain
    ell R r 1 17 hell hR hr
    (by norm_num) (by norm_num)
    actualOneOrbitTerminalRadiation hz
    (fun u _ => actual_one_orbit_terminal_radiation_norm_le_one u)
    (fun u hu => actual_one_orbit_terminal_quartic_bubble_envelope u hu)
  calc
    _ ≤ (2 * radialHartreeRowBoundConstant * 17 * (1:ℝ)^3) *
        ell ^ 2 * Real.sqrt ell := h
    _ = (34 * radialHartreeRowBoundConstant) *
        ell ^ 2 * Real.sqrt ell := by ring

/-- The *same* nonzero physical terminal radiation produces an
original L^(2,sigma) source, with no postulated Riesz envelope,
pointwise amplitude constant, or source measurability premise. -/
theorem actual_one_orbit_terminal_nonlocal_source_weightedL2
    (ell R sigma : ℝ)
    (hell : 0 < ell) (hR : 0 < R)
    (hSigmaLo : 3 / 2 < sigma) (hSigmaHi : sigma < 2) :
    MemLp
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualHartreeNonlocalCutoffError
          R ell actualOneOrbitTerminalRadiation r‖)
      2 halfLineMeasure := by
  have hz : Measurable actualOneOrbitTerminalRadiation :=
    (Complex.continuous_ofReal.comp
      actual_one_orbit_terminal_bump_smooth.continuous).measurable
  exact actual_Hartree_nonlocal_cutoff_source_mem_manuscript_weightedL2
    ell R 1 17 sigma hell hR
    (by norm_num) (by norm_num)
    hSigmaLo hSigmaHi actualOneOrbitTerminalRadiation hz
    (fun u _ => actual_one_orbit_terminal_radiation_norm_le_one u)
    (fun u hu => actual_one_orbit_terminal_quartic_bubble_envelope u hu)
    (actual_Hartree_nonlocal_cutoff_error_measurable
      R ell actualOneOrbitTerminalRadiation hz)

end HBL.TypeIIDynamicSelection
