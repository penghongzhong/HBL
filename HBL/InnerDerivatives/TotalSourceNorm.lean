import HBL.WeightedFreeGreenInjective
import HBL.InnerDerivatives.SourceNorm
import HBL.InnerEstimates.FirstMomentNorm
import HBL.InnerEstimates.GreenPrimitiveNorm
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem inner_totalSource_integral_norm_le (g : RealL2 halfLineMeasure)
    (sigma : ℝ) (hsigma : 3 / 2 < sigma) (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    let S := fun r => weightedGreenDecay r * g r + F r
    Integrable S halfLineMeasure ∧ Integrable (fun r => r * S r) halfLineMeasure ∧
      (∫ r, ‖S r‖ ∂halfLineMeasure) + (∫ r, ‖r * S r‖ ∂halfLineMeasure) ≤
        innerGreenDerivativeMajorant * ‖g‖ + innerSourceDerivativeMajorant sigma hsigma * innerWeightedNorm sigma F := by
  let A := fun r => weightedGreenDecay r * g r
  have hA := weightedGreen_source_integrable g
  have hMA := weightedGreen_source_first_moment_integrable g
  have hiF := weightedSource_integrable sigma (by linarith) F hF
  have hMF := weightedSource_firstMoment_integrable sigma hsigma F hF
  have heq : (fun r => r * (A r + F r)) = (fun r => r * A r + r * F r) := by funext r; ring
  refine ⟨hA.add hiF, ?_, ?_⟩
  · rw [show (fun r => r * (weightedGreenDecay r * g r + F r)) = (fun r => r * A r + r * F r) from heq]
    exact hMA.add hMF
  · have h0 : (∫ r, ‖A r + F r‖ ∂halfLineMeasure) ≤
        (∫ r, ‖A r‖ ∂halfLineMeasure) + (∫ r, ‖F r‖ ∂halfLineMeasure) := by
      rw [← integral_add hA.norm hiF.norm]
      exact integral_mono (hA.add hiF).norm (hA.norm.add hiF.norm) (fun r => norm_add_le _ _)
    have h1 : (∫ r, ‖r * (A r + F r)‖ ∂halfLineMeasure) ≤
        (∫ r, ‖r * A r‖ ∂halfLineMeasure) + (∫ r, ‖r * F r‖ ∂halfLineMeasure) := by
      simp_rw [mul_add]
      rw [← integral_add hMA.norm hMF.norm]
      exact integral_mono (hMA.add hMF).norm (hMA.norm.add hMF.norm) (fun r => norm_add_le _ _)
    have hAn := inner_integral_norm_mul_le weightedGreenDecay g weightedGreenDecay_memLp_two (Lp.memLp g)
    simp only [Lp.toLp_coeFn] at hAn
    have hMAn : (∫ r, ‖r * A r‖ ∂halfLineMeasure) ≤ innerGreenMajorantNorm * ‖g‖ := by
      have he : (∫ r, ‖r * A r‖ ∂halfLineMeasure) = weightedGreenPrimitiveBound g := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        simp only [A, weightedGreenOutputMajorant, abs_of_pos (show 0 < r from hr), mul_assoc]
      rw [he]
      exact inner_greenPrimitiveBound_le g
    have hFn := inner_source_integral_norm_le sigma (by linarith) F hF
    have hMFn := inner_firstMoment_norm_le sigma hsigma F hF
    dsimp only
    change (∫ r, ‖A r + F r‖ ∂halfLineMeasure) + (∫ r, ‖r * (A r + F r)‖ ∂halfLineMeasure) ≤ _
    unfold innerGreenDerivativeMajorant innerSourceDerivativeMajorant
    nlinarith
end HBL.Modulation.Monopole
