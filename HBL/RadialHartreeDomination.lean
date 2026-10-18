import HBL.MonopoleHartreePotentialBound

/-! Domination by the proved bubble-squared row, with absolute convergence. -/

noncomputable section
open Set MeasureTheory
namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The actual normalized bubble-squared row bound. -/
def radialHartreeRowBoundConstant : ℝ :=
  2 * Real.pi * hartreeKappa * radialHartreeBubbleBoundConstant

theorem radialHartreeRowBoundConstant_pos : 0 < radialHartreeRowBoundConstant := by
  have h := radialHartreeBubbleBoundConstant_pos
  unfold radialHartreeRowBoundConstant hartreeKappa
  positivity

/-- A measurable density dominated by `M W²` has an absolutely convergent
actual potential and a radius-independent bound. -/
theorem radialHartreePotential_bubble_sq_domination
    (F : ℝ → ℝ) (hf : Measurable F) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ rho, 0 < rho → |F rho| ≤ M * bubble rho ^ 2)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi 0) ∧
      |radialHartreePotential F r| ≤ radialHartreeRowBoundConstant * M := by
  have hrow := radialHartreeBubble_integrable_bound hr
  have hlogmeas : Measurable (hartreeRadialLog r) := by
    unfold hartreeRadialLog
    fun_prop
  have hmeas := (measurable_id.mul hlogmeas).mul hf
  have hpoint : ∀ rho ∈ Ioi (0 : ℝ),
      |rho * hartreeRadialLog r rho * F rho| ≤
        M * (rho * hartreeRadialLog r rho * bubble rho ^ 2) := by
    intro rho hrho
    have hl := hartreeRadialLog_nonneg r rho hr hrho
    rw [abs_mul, abs_mul, abs_of_pos hrho, abs_of_nonneg hl]
    calc
      rho * hartreeRadialLog r rho * |F rho| ≤
          rho * hartreeRadialLog r rho * (M * bubble rho ^ 2) :=
        mul_le_mul_of_nonneg_left (hbound rho hrho) (mul_nonneg hrho.le hl)
      _ = _ := by ring
  have hint : IntegrableOn (fun rho => rho * hartreeRadialLog r rho * F rho)
      (Ioi 0) := by
    apply (hrow.1.const_mul M).mono' hmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    rw [Real.norm_eq_abs]
    exact hpoint rho hrho
  refine ⟨hint, ?_⟩
  have hInt : |∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho * F rho| ≤
      M * (r * radialHartreeBubbleBoundConstant) := by
    calc
      |∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho * F rho| ≤
          ∫ rho in Ioi (0 : ℝ), |rho * hartreeRadialLog r rho * F rho| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ rho in Ioi (0 : ℝ), M * (rho * hartreeRadialLog r rho * bubble rho ^ 2) := by
        apply integral_mono_ae hint.abs (hrow.1.const_mul M)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
        exact hpoint rho hrho
      _ = M * ∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho * bubble rho ^ 2 := by
        rw [integral_const_mul]
      _ ≤ M * (r * radialHartreeBubbleBoundConstant) :=
        mul_le_mul_of_nonneg_left hrow.2 hM
  have hcoeff : 0 ≤ 2 * Real.pi * hartreeKappa / r := by
    unfold hartreeKappa
    positivity
  unfold radialHartreePotential
  rw [abs_mul, abs_of_nonneg hcoeff]
  calc
    (2 * Real.pi * hartreeKappa / r) *
        |∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho * F rho| ≤
        (2 * Real.pi * hartreeKappa / r) * (M * (r * radialHartreeBubbleBoundConstant)) :=
      mul_le_mul_of_nonneg_left hInt hcoeff
    _ = radialHartreeRowBoundConstant * M := by
      unfold radialHartreeRowBoundConstant
      field_simp

/-- The actual truncated radial profile is measurable even at the total quotient's origin. -/
theorem monopoleInnerRadialProfile_measurable (R : ℝ) :
    Measurable (monopoleInnerRadialProfile R) := by
  have hc : Continuous (fun rho : ℝ => 1 - cutoff (rho / R)) :=
    continuous_const.sub
      (cutoff_contDiff_infty.continuous.comp (continuous_id.div_const R))
  exact (hc.mul monopoleProfile_continuous).measurable.div measurable_id

theorem bubble_abs_le_one (r : ℝ) : |bubble r| ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (1 + r ^ 2) := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + r ^ 2 by nlinarith [sq_nonneg r])
    simpa only [Real.sqrt_one] using hh
  unfold bubble
  rw [abs_of_nonneg (by positivity)]
  exact (inv_le_one₀ (by positivity)).2 hs

/-- The constant and linear densities in the actual Hartree expansion have
absolutely convergent, uniformly bounded potentials. -/
theorem monopoleHartreeBaseLinear_control {R r : ℝ} (hr : 0 < r) :
    (IntegrableOn (fun rho => rho * hartreeRadialLog r rho * bubble rho ^ 4) (Ioi 0) ∧
      |radialHartreePotential (fun rho => bubble rho ^ 4) r| ≤ radialHartreeRowBoundConstant) ∧
    (IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
        (bubble rho ^ 3 * monopoleInnerRadialProfile R rho)) (Ioi 0) ∧
      |radialHartreePotential (fun rho => bubble rho ^ 3 * monopoleInnerRadialProfile R rho) r| ≤
        radialHartreeRowBoundConstant * monopoleRadialBoundConstant) := by
  have hw : Measurable bubble := bubble_contDiff_infty.continuous.measurable
  have hb0 : ∀ rho : ℝ, 0 < rho → |bubble rho ^ 4| ≤ 1 * bubble rho ^ 2 := by
    intro rho _hrho
    have hW : 0 ≤ bubble rho := by unfold bubble; positivity
    have hW1 : bubble rho ≤ 1 := (le_abs_self _).trans (bubble_abs_le_one rho)
    rw [abs_pow, abs_of_nonneg hW, one_mul]
    have hs : bubble rho ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (bubble rho), mul_nonneg (sq_nonneg (bubble rho)) (sub_nonneg.mpr hs)]
  have hb1 : ∀ rho : ℝ, 0 < rho →
      |bubble rho ^ 3 * monopoleInnerRadialProfile R rho| ≤
        monopoleRadialBoundConstant * bubble rho ^ 2 := by
    intro rho hrho
    have hW : 0 ≤ bubble rho := by unfold bubble; positivity
    have hW1 : bubble rho ≤ 1 := (le_abs_self _).trans (bubble_abs_le_one rho)
    have hX := monopoleInnerRadialProfile_abs_le (R := R) hrho
    rw [abs_mul, abs_pow, abs_of_nonneg hW]
    calc
      bubble rho ^ 3 * |monopoleInnerRadialProfile R rho| ≤
          bubble rho ^ 3 * monopoleRadialBoundConstant := by gcongr
      _ ≤ bubble rho ^ 2 * monopoleRadialBoundConstant := by
        apply mul_le_mul_of_nonneg_right _ monopoleRadialBoundConstant_pos.le
        nlinarith [sq_nonneg (bubble rho), mul_nonneg (sq_nonneg (bubble rho)) (sub_nonneg.mpr hW1)]
      _ = _ := by ring
  have h0 := radialHartreePotential_bubble_sq_domination
    (fun rho => bubble rho ^ 4) (hw.pow_const 4) (show (0 : ℝ) ≤ 1 by norm_num) hb0 hr
  have h1 := radialHartreePotential_bubble_sq_domination
    (fun rho => bubble rho ^ 3 * monopoleInnerRadialProfile R rho)
    ((hw.pow_const 3).mul (monopoleInnerRadialProfile_measurable R))
    monopoleRadialBoundConstant_pos.le hb1 hr
  exact ⟨by simpa only [mul_one] using h0, h1⟩

end HBL.Modulation.Monopole
