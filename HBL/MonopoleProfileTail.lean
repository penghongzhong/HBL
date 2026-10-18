import HBL.MonopoleFredholmAsymptotics

/-!
The actual monopole profile and its radial quotient, with the quantitative
far-field expansion inherited from the normalized Fredholm remainder.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole

open HBL.Modulation.AffineTail

/-- The conjugated monopole profile `ξ = q_log + ℓ q_aff + h`. -/
def monopoleProfile (r : ℝ) : ℝ :=
  monopoleLogModel r + monopoleAffineSlope * model r + monopoleRemainder r

/-- The radial profile `Ξ = ξ/r`, used on the positive half-line. -/
def monopoleRadialProfile (r : ℝ) : ℝ :=
  monopoleProfile r / r

theorem monopoleProfile_eq_log_affine_remainder
    {r : ℝ} (hr : 2 < r) :
    monopoleProfile r =
      Real.log r + monopoleAffineSlope * r + monopoleRemainder r := by
  unfold monopoleProfile
  rw [monopoleLogModel_eq_log_of_two_le r hr.le,
    model_eq_id_of_two_le r hr.le]

/-- The conjugated profile has a first-moment constant and an `O(r⁻¹)`
error beyond its logarithmic and affine terms. -/
theorem monopoleProfile_sub_asymptotic_abs_le
    {r : ℝ} (hr : 2 < r) :
    |monopoleProfile r -
      (Real.log r + monopoleAffineSlope * r + monopoleTailConstant)| ≤
        monopoleSourceDecayConstant / r := by
  calc
    |monopoleProfile r -
        (Real.log r + monopoleAffineSlope * r + monopoleTailConstant)| =
        |monopoleRemainder r - monopoleTailConstant| := by
      rw [monopoleProfile_eq_log_affine_remainder hr]
      congr 1
      ring
    _ ≤ monopoleSourceDecayConstant / r := by
      simpa only [div_eq_mul_inv] using
        monopoleRemainder_sub_tailConstant_abs_le hr

theorem monopoleRadialProfile_eq_slope_add_log_remainder_div
    {r : ℝ} (hr : 2 < r) :
    monopoleRadialProfile r =
      monopoleAffineSlope + (Real.log r + monopoleRemainder r) / r := by
  have hrne : r ≠ 0 := by linarith
  unfold monopoleRadialProfile
  rw [monopoleProfile_eq_log_affine_remainder hr]
  calc
    (Real.log r + monopoleAffineSlope * r + monopoleRemainder r) / r =
        (monopoleAffineSlope * r + (Real.log r + monopoleRemainder r)) / r := by
      congr 1
      ring
    _ = monopoleAffineSlope * r / r +
        (Real.log r + monopoleRemainder r) / r := add_div _ _ _
    _ = monopoleAffineSlope + (Real.log r + monopoleRemainder r) / r := by
      rw [mul_div_cancel_right₀ _ hrne]

/-- Division by the radius improves the error to `O(r⁻²)` in the actual
radial monopole profile. -/
theorem monopoleRadialProfile_sub_asymptotic_abs_le
    {r : ℝ} (hr : 2 < r) :
    |monopoleRadialProfile r -
      (monopoleAffineSlope + (Real.log r + monopoleTailConstant) / r)| ≤
        monopoleSourceDecayConstant / r ^ 2 := by
  have hr0 : 0 < r := by linarith
  calc
    |monopoleRadialProfile r -
        (monopoleAffineSlope + (Real.log r + monopoleTailConstant) / r)| =
        |monopoleRemainder r - monopoleTailConstant| / r := by
      rw [monopoleRadialProfile_eq_slope_add_log_remainder_div hr]
      have heq :
          monopoleAffineSlope + (Real.log r + monopoleRemainder r) / r -
            (monopoleAffineSlope + (Real.log r + monopoleTailConstant) / r) =
          (monopoleRemainder r - monopoleTailConstant) / r := by ring
      rw [heq, abs_div, abs_of_pos hr0]
    _ ≤ (monopoleSourceDecayConstant / r) / r := by
      apply div_le_div_of_nonneg_right _ hr0.le
      simpa only [div_eq_mul_inv] using
        monopoleRemainder_sub_tailConstant_abs_le hr
    _ = monopoleSourceDecayConstant / r ^ 2 := by
      rw [div_div, pow_two]

theorem monopoleProfile_sub_log_affine_tendsto_tailConstant :
    Tendsto
      (fun r : ℝ => monopoleProfile r - (Real.log r + monopoleAffineSlope * r))
      atTop (𝓝 monopoleTailConstant) := by
  apply monopoleRemainder_tendsto_tailConstant.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with r hr
  rw [monopoleProfile_eq_log_affine_remainder hr]
  ring

theorem monopoleRadialProfile_tendsto_affineSlope :
    Tendsto monopoleRadialProfile atTop (𝓝 monopoleAffineSlope) := by
  have hlog : Tendsto (fun r : ℝ => Real.log r / r) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hrem : Tendsto (fun r : ℝ => monopoleRemainder r / r) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      monopoleRemainder_tendsto_tailConstant.mul tendsto_inv_atTop_zero
  have hsum : Tendsto
      (fun r : ℝ => monopoleAffineSlope + (Real.log r + monopoleRemainder r) / r)
      atTop (𝓝 monopoleAffineSlope) := by
    simpa only [add_div, add_zero] using
      tendsto_const_nhds.add (hlog.add hrem)
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with r hr
  exact (monopoleRadialProfile_eq_slope_add_log_remainder_div hr).symm

/-- The actual radial profile tends to the slope fixed by the threshold
charge calculation. -/
theorem monopoleRadialProfile_tendsto_neg_pi_div_eight :
    Tendsto monopoleRadialProfile atTop (𝓝 (-(Real.pi / 8))) := by
  simpa only [monopoleAffineSlope_eq_neg_pi_div_eight] using
    monopoleRadialProfile_tendsto_affineSlope

theorem monopoleProfile_zero : monopoleProfile 0 = 0 := by
  rw [monopoleProfile, monopoleLogModel_zero, model_zero]
  simp only [mul_zero, zero_add]
  rw [monopoleRemainder_eq_halfLineMinGreen, halfLineMinGreen_zero]

end HBL.Modulation.Monopole
