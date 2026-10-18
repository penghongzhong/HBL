import HBL.MonopoleProfileTail

/-! A uniform bound for the actual radial monopole on the whole positive half-line. -/

noncomputable section
open Set MeasureTheory

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The weighted source's genuine L1 norm controls the Green remainder divided by radius. -/
private theorem weightedGreenPrimitive_abs_le_radius
    (f : RealL2 halfLineMeasure) {r : ℝ} (hr : 0 < r) :
    |weightedGreenPrimitive f r| ≤ (weightedGreenLipschitzConstant f : ℝ) * r := by
  have hz : weightedGreenPrimitive f 0 = 0 := by
    unfold weightedGreenPrimitive
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    rw [min_eq_left hrho.le, zero_mul]
    rfl
  have hb := (weightedGreenPrimitive_lipschitz f).dist_le_mul r 0
  simpa only [hz, Real.dist_eq, sub_zero, abs_of_pos hr] using hb

/-- An explicit finite bound from the actual Fredholm datum and the fixed models. -/
def monopoleRadialBoundConstant : ℝ :=
  1 + |monopoleAffineSlope| +
    (weightedGreenLipschitzConstant monopoleTotalDatum : ℝ)

theorem monopoleRadialBoundConstant_pos : 0 < monopoleRadialBoundConstant := by
  unfold monopoleRadialBoundConstant
  positivity

/-- The constructed radial profile is bounded for every positive radius,
including arbitrarily small radii. No profile bound or source integrability is assumed. -/
theorem monopoleRadialProfile_abs_le {r : ℝ} (hr : 0 < r) :
    |monopoleRadialProfile r| ≤ monopoleRadialBoundConstant := by
  have hm₀ : 0 ≤ model r :=
    mul_nonneg (show 0 ≤ cutoff r from Real.smoothTransition.nonneg _) hr.le
  have hm : model r ≤ r := by
    exact mul_le_of_le_one_left hr.le (show cutoff r ≤ 1 from Real.smoothTransition.le_one _)
  have hl : |monopoleLogModel r| ≤ r := (monopoleLogModel_abs_le_model r).trans hm
  have hrem : |monopoleRemainder r| ≤
      (weightedGreenLipschitzConstant monopoleTotalDatum : ℝ) * r :=
    weightedGreenPrimitive_abs_le_radius monopoleTotalDatum hr
  have hprofile : |monopoleProfile r| ≤ monopoleRadialBoundConstant * r := by
    calc
      |monopoleProfile r| ≤ |monopoleLogModel r| +
          |monopoleAffineSlope * model r| + |monopoleRemainder r| := by
        unfold monopoleProfile
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ r + |monopoleAffineSlope| * r +
          (weightedGreenLipschitzConstant monopoleTotalDatum : ℝ) * r := by
        rw [abs_mul, abs_of_nonneg hm₀]
        exact add_le_add (add_le_add hl
          (mul_le_mul_of_nonneg_left hm (abs_nonneg _))) hrem
      _ = monopoleRadialBoundConstant * r := by
        unfold monopoleRadialBoundConstant
        ring
  rw [monopoleRadialProfile, abs_div, abs_of_pos hr]
  exact (div_le_iff₀ hr).mpr hprofile

end HBL.Modulation.Monopole
