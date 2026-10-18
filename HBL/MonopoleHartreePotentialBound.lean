import HBL.MonopoleHartreeDensityDecay
import HBL.RadialHartreePotential
import HBL.RadialHartreeBubbleBound

/-! The actual nonlocal quartic density remainder has a uniform quadratic potential. -/

noncomputable section
open Set MeasureTheory

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- An amplitude-independent constant from the actual monopole and a fixed kernel row. -/
def monopoleHartreePotentialBoundConstant : ℝ :=
  2 * Real.pi * hartreeKappa * monopoleHartreeDensityDecayConstant *
    radialHartreeBubbleBoundConstant

/-- Absolute convergence and a uniform quadratic bound for the genuine radial
potential of the constructed profile's fourth-power Taylor remainder. -/
theorem monopoleHartreeDensityPotential_quadratic_control {c r : ℝ}
    (hc : 0 < |c|) (hc1 : |c| ≤ 1) (hr : 0 < r) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c rho) (Ioi 0) ∧
    |radialHartreePotential
      (monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c) r| ≤
      monopoleHartreePotentialBoundConstant * c ^ 2 := by
  let M := monopoleHartreeDensityDecayConstant * c ^ 2
  have hB := monopoleRadialBoundConstant_pos.le
  have hM : 0 ≤ M := by
    dsimp [M, monopoleHartreeDensityDecayConstant]
    positivity
  have hrow := radialHartreeBubble_integrable_bound hr
  have hlogmeas : Measurable (hartreeRadialLog r) := by
    unfold hartreeRadialLog
    fun_prop
  have hmeas := (measurable_id.mul hlogmeas).mul
    (monopoleHartreeDensityRemainder_measurable (monopoleQuadraticRadius c) c)
  have hpoint : ∀ rho ∈ Ioi (0 : ℝ),
      |rho * hartreeRadialLog r rho *
        monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c rho| ≤
        M * (rho * hartreeRadialLog r rho * bubble rho ^ 2) := by
    intro rho hrho
    have hl := hartreeRadialLog_nonneg r rho hr hrho
    rw [abs_mul, abs_mul, abs_of_pos hrho, abs_of_nonneg hl]
    calc
      rho * hartreeRadialLog r rho *
          |monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c rho| ≤
          rho * hartreeRadialLog r rho * (M * bubble rho ^ 2) :=
        mul_le_mul_of_nonneg_left
          (monopoleHartreeDensityRemainder_weighted_abs_le hc hc1 hrho)
          (mul_nonneg hrho.le hl)
      _ = _ := by ring
  have hint : IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c rho) (Ioi 0) := by
    apply (hrow.1.const_mul M).mono' hmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    rw [Real.norm_eq_abs]
    exact hpoint rho hrho
  refine ⟨hint, ?_⟩
  have hInt : |∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho *
      monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c rho| ≤
      M * (r * radialHartreeBubbleBoundConstant) := by
    calc
      |∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho *
          monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c rho| ≤
          ∫ rho in Ioi (0 : ℝ), |rho * hartreeRadialLog r rho *
            monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c rho| :=
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
        |∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho *
          monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c rho| ≤
        (2 * Real.pi * hartreeKappa / r) * (M * (r * radialHartreeBubbleBoundConstant)) :=
      mul_le_mul_of_nonneg_left hInt hcoeff
    _ = monopoleHartreePotentialBoundConstant * c ^ 2 := by
      dsimp [M, monopoleHartreePotentialBoundConstant]
      field_simp

end HBL.Modulation.Monopole
