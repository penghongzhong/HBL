import HBL.AffineTailLogIBPFinite

/-!
Finite-interval rational decomposition of the derivative term produced
by logarithmic integration by parts.  The Cauchy singularity is explicitly
excluded; the two ordinary rational kernels are L1 on all of R.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- Exact rational decomposition of the weighted Cauchy kernel. -/
theorem pv_weight_decomposition
    (r rho : ℝ) (hsep : r ^ 2 - rho ^ 2 ≠ 0) :
    (2 * r / (r ^ 2 - rho ^ 2)) * radialLogPrimitive rho =
      (r / 2) *
        ((r ^ 2 / (1 + r ^ 2) ^ 2) * (1 + rho ^ 2)⁻¹ -
         (1 / (1 + r ^ 2)) * ((1 + rho ^ 2) ^ 2)⁻¹ +
         (r ^ 2 / (1 + r ^ 2) ^ 2) * (r ^ 2 - rho ^ 2)⁻¹) := by
  have hr : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
  have hh : (1 + rho ^ 2 : ℝ) ≠ 0 := by positivity
  unfold radialLogPrimitive
  field_simp [hr, hh, hsep] <;> ring

/-- A truly finite-interval identity: no Cauchy principal value is
assumed and each of the three terms is integrable on this interval. -/
theorem pv_weight_interval_decomposition
    (r a b : ℝ)
    (havoid : ∀ rho ∈ Set.uIcc a b, r ^ 2 - rho ^ 2 ≠ 0) :
    (∫ rho in a..b,
      (2 * r / (r ^ 2 - rho ^ 2)) * radialLogPrimitive rho) =
      (r / 2) *
        ((r ^ 2 / (1 + r ^ 2) ^ 2) *
            (∫ rho in a..b, (1 + rho ^ 2)⁻¹) -
          (1 / (1 + r ^ 2)) *
            (∫ rho in a..b, ((1 + rho ^ 2) ^ 2)⁻¹) +
          (r ^ 2 / (1 + r ^ 2) ^ 2) *
            (∫ rho in a..b, (r ^ 2 - rho ^ 2)⁻¹)) := by
  let A : ℝ := r ^ 2 / (1 + r ^ 2) ^ 2
  let B : ℝ := 1 / (1 + r ^ 2)
  have hI1 : IntervalIntegrable (fun rho : ℝ => (1 + rho ^ 2)⁻¹)
      volume a b := by
    have hc : Continuous (fun rho : ℝ => (1 + rho ^ 2)⁻¹) := by
      apply Continuous.inv₀ (by fun_prop)
      intro x
      positivity
    exact hc.intervalIntegrable a b
  have hI2 : IntervalIntegrable (fun rho : ℝ => ((1 + rho ^ 2) ^ 2)⁻¹)
      volume a b := by
    have hc : Continuous (fun rho : ℝ => ((1 + rho ^ 2) ^ 2)⁻¹) := by
      apply Continuous.inv₀ (by fun_prop)
      intro x
      positivity
    exact hc.intervalIntegrable a b
  have hIk : IntervalIntegrable (fun rho : ℝ => (r ^ 2 - rho ^ 2)⁻¹)
      volume a b :=
    ((continuous_const.sub (continuous_id.pow 2)).continuousOn.inv₀
      havoid).intervalIntegrable
  have h1 := hI1.const_mul A
  have h2 := hI2.const_mul B
  have h3 := hIk.const_mul A
  have hsub := h1.sub h2
  calc
    (∫ rho in a..b,
      (2 * r / (r ^ 2 - rho ^ 2)) * radialLogPrimitive rho) =
        ∫ rho in a..b,
          (r / 2) *
            (A * (1 + rho ^ 2)⁻¹ -
              B * ((1 + rho ^ 2) ^ 2)⁻¹ +
              A * (r ^ 2 - rho ^ 2)⁻¹) := by
          apply intervalIntegral.integral_congr
          intro rho hρ
          simpa only [A, B] using pv_weight_decomposition r rho (havoid rho hρ)
    _ = (r / 2) *
          (∫ rho in a..b,
            A * (1 + rho ^ 2)⁻¹ -
              B * ((1 + rho ^ 2) ^ 2)⁻¹ +
              A * (r ^ 2 - rho ^ 2)⁻¹) := by
          rw [intervalIntegral.integral_const_mul]
    _ = (r / 2) *
          ((∫ rho in a..b,
            A * (1 + rho ^ 2)⁻¹ -
              B * ((1 + rho ^ 2) ^ 2)⁻¹) +
           (∫ rho in a..b,
            A * (r ^ 2 - rho ^ 2)⁻¹)) := by
          rw [intervalIntegral.integral_add hsub h3]
    _ = (r / 2) *
          (((∫ rho in a..b, A * (1 + rho ^ 2)⁻¹) -
            (∫ rho in a..b, B * ((1 + rho ^ 2) ^ 2)⁻¹)) +
           (∫ rho in a..b, A * (r ^ 2 - rho ^ 2)⁻¹)) := by
          rw [intervalIntegral.integral_sub h1 h2]
    _ = _ := by
          simp only [intervalIntegral.integral_const_mul] <;> rfl

end HBL.Modulation.AffineTail
