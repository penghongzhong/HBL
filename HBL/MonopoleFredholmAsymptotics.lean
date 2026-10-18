import HBL.MonopoleFredholmDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
The far-field constant and quantitative Green tail for the first monopole
correction.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- First moment of the remainder source; this is the constant approached
by the zero-slope Green primitive. -/
def monopoleTailConstant : ℝ :=
  ∫ rho : ℝ, rho * monopoleRemainderSource rho ∂halfLineMeasure

theorem monopoleRemainderSource_firstMoment_ae :
    (fun rho : ℝ => rho * monopoleRemainderSource rho)
      =ᵐ[halfLineMeasure]
        fun rho => weightedGreenOutputMajorant rho * monopoleTotalDatum rho := by
  filter_upwards [weightedGreen_totalDatum_ae_source,
    ae_restrict_mem measurableSet_Ioi] with rho hsource hrho
  rw [← hsource]
  unfold weightedGreenOutputMajorant
  rw [abs_of_pos hrho]
  ring

theorem monopoleRemainderSource_firstMoment_integrable :
    Integrable (fun rho : ℝ => rho * monopoleRemainderSource rho)
      halfLineMeasure := by
  exact (weightedGreenOutputMajorant_mul_integrable monopoleTotalDatum).congr
    monopoleRemainderSource_firstMoment_ae.symm

theorem monopoleRemainder_minKernel_integrable (r : ℝ) :
    Integrable (fun rho : ℝ => min r rho * monopoleRemainderSource rho)
      halfLineMeasure := by
  apply (weightedGreenPrimitive_integrable_kernel monopoleTotalDatum r).congr
  filter_upwards [weightedGreen_totalDatum_ae_source] with rho hsource
  rw [hsource]

/-- On a positive outgoing interval the half-line restricted measure is
just Lebesgue measure restricted to that interval. -/
theorem halfLineMeasure_restrict_Ioi {r : ℝ} (hr : 0 ≤ r) :
    halfLineMeasure.restrict (Ioi r) = volume.restrict (Ioi r) := by
  unfold halfLineMeasure
  exact Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hr)

/-- Exact remainder after subtracting the limiting constant. -/
theorem monopoleRemainder_sub_tailConstant
    {r : ℝ} (_hr : 0 < r) :
    monopoleRemainder r - monopoleTailConstant =
      ∫ rho in Ioi r, (r - rho) * monopoleRemainderSource rho
        ∂halfLineMeasure := by
  rw [monopoleRemainder_eq_halfLineMinGreen]
  unfold halfLineMinGreen monopoleTailConstant
  rw [← integral_sub (monopoleRemainder_minKernel_integrable r)
    monopoleRemainderSource_firstMoment_integrable]
  rw [← integral_indicator (μ := halfLineMeasure) (s := Ioi r)
    measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with rho
  by_cases hρ : rho ∈ Ioi r
  · rw [indicator_of_mem hρ, min_eq_left hρ.le]
    ring
  · rw [indicator_of_notMem hρ, min_eq_right (le_of_not_gt hρ)]
    ring

theorem monopoleRemainder_tailIntegrand_integrableOn
    {r : ℝ} (_hr : 0 < r) :
    IntegrableOn
      (fun rho : ℝ => (r - rho) * monopoleRemainderSource rho)
      (Ioi r) halfLineMeasure := by
  have hdiff : Integrable
      (fun rho : ℝ =>
        min r rho * monopoleRemainderSource rho -
          rho * monopoleRemainderSource rho) halfLineMeasure :=
    (monopoleRemainder_minKernel_integrable r).sub
      monopoleRemainderSource_firstMoment_integrable
  refine (hdiff.integrableOn.congr_fun ?_ measurableSet_Ioi)
  intro rho hρ
  dsimp only
  rw [min_eq_left hρ.le]
  ring

theorem rpow_neg_two_eq_inv_sq {r : ℝ} (hr : 0 < r) :
    r ^ (-2 : ℝ) = (r ^ 2)⁻¹ := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg hr.le, Real.rpow_two]

theorem integral_Ioi_rpow_neg_two {r : ℝ} (hr : 0 < r) :
    (∫ rho : ℝ in Ioi r, rho ^ (-2 : ℝ)) = r⁻¹ := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr]
  norm_num
  rw [Real.rpow_neg_one]

/-- The tail is in fact `O(r⁻¹)`, which is stronger than the logarithmic
loss recorded in the manuscript statement. -/
theorem monopoleRemainder_sub_tailConstant_abs_le
    {r : ℝ} (hr : 2 < r) :
    |monopoleRemainder r - monopoleTailConstant| ≤
      monopoleSourceDecayConstant * r⁻¹ := by
  rw [monopoleRemainder_sub_tailConstant (by linarith : 0 < r)]
  have hmajorVolume : IntegrableOn
      (fun rho : ℝ => monopoleSourceDecayConstant * rho ^ (-2 : ℝ))
      (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-2 : ℝ) < -1) (by linarith : 0 < r)).const_mul _
  have hmeasure := halfLineMeasure_restrict_Ioi (le_of_lt (by linarith : 0 < r))
  have hmajor : IntegrableOn
      (fun rho : ℝ => monopoleSourceDecayConstant * rho ^ (-2 : ℝ))
      (Ioi r) halfLineMeasure := by
    unfold IntegrableOn
    rw [hmeasure]
    exact hmajorVolume
  calc
    |∫ rho in Ioi r, (r - rho) * monopoleRemainderSource rho
        ∂halfLineMeasure| ≤
        ∫ rho in Ioi r,
          |(r - rho) * monopoleRemainderSource rho|
          ∂halfLineMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ rho in Ioi r,
          monopoleSourceDecayConstant * rho ^ (-2 : ℝ)
          ∂halfLineMeasure := by
      apply integral_mono_ae
      · exact (monopoleRemainder_tailIntegrand_integrableOn
          (by linarith : 0 < r)).norm
      · exact hmajor
      · filter_upwards [ae_restrict_of_ae monopoleRemainderSource_ae_norm_le,
          ae_restrict_mem measurableSet_Ioi] with rho hsource hρ
        change r < rho at hρ
        have hρ0 : 0 < rho := by linarith
        have hdist : |r - rho| ≤ rho := by
          rw [abs_of_nonpos (by linarith)]
          linarith
        have hdecay : bubble rho ^ 3 ≤ rho⁻¹ ^ 3 :=
          bubble_pow_three_le_inv_pow_three rho hρ0
        have hC0 := monopoleSourceDecayConstant_nonneg
        rw [abs_mul]
        calc
          |r - rho| * |monopoleRemainderSource rho| ≤
              rho * (monopoleSourceDecayConstant * bubble rho ^ 3) :=
            mul_le_mul hdist (hsource (by linarith)) (abs_nonneg _)
              (by linarith)
          _ ≤ rho * (monopoleSourceDecayConstant * rho⁻¹ ^ 3) := by
            gcongr
          _ = monopoleSourceDecayConstant * rho ^ (-2 : ℝ) := by
            rw [rpow_neg_two_eq_inv_sq hρ0]
            field_simp [ne_of_gt hρ0]
    _ = ∫ rho in Ioi r,
          monopoleSourceDecayConstant * rho ^ (-2 : ℝ) := by
      rw [hmeasure]
    _ = monopoleSourceDecayConstant *
          (∫ rho in Ioi r, rho ^ (-2 : ℝ)) := by
      rw [integral_const_mul]
    _ = monopoleSourceDecayConstant * r⁻¹ := by
      rw [integral_Ioi_rpow_neg_two (by linarith : 0 < r)]

/-- The canonical Fredholm remainder converges to its first-moment
constant at positive infinity. -/
theorem monopoleRemainder_tendsto_tailConstant :
    Tendsto monopoleRemainder atTop (𝓝 monopoleTailConstant) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hmajor : Tendsto
      (fun r : ℝ => monopoleSourceDecayConstant * r⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_inv_atTop_zero.const_mul monopoleSourceDecayConstant
  refine squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) ?_ hmajor
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with r hr
  simpa only [Real.dist_eq] using
    monopoleRemainder_sub_tailConstant_abs_le hr

end HBL.Modulation.Monopole
