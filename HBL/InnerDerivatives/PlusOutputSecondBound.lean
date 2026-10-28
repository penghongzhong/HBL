import HBL.InnerDerivatives.PlusSecondBound
import HBL.InnerDerivatives.AffineSecondWeighted
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

def innerPlusOutputSecondConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  innerPlusSecondDerivativeConstant sigma hLower hUpper + (2 * ‖weightedSourceResonanceL2 sigma (by linarith)‖) * innerWeightedNorm sigma affineModelSecondDerivative

theorem normalizedPlusOutput_second_derivative_bound
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) :
    InWeightedL2 sigma (deriv (deriv (normalizedPlusOutput sigma hLower hUpper F hF))) ∧
    innerWeightedNorm sigma (deriv (deriv (normalizedPlusOutput sigma hLower hUpper F hF))) ≤
      innerPlusOutputSecondConstant sigma hLower hUpper * innerWeightedNorm sigma F := by
  have hc := plus_innerGreenRepresentative_classical
    (normalizedPlusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure)
    sigma (by linarith) (correctedPlusSource F)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF) (correctedPlusSource_continuous F hcF)
    (normalizedPlusInner_equation sigma hLower hUpper F hF)
  have hq := normalizedPlusRemainder_second_derivative_bound sigma hLower hUpper F hF hcF
  have hb := affineRestore_second_weighted_bound sigma (normalizedPlusRemainder sigma hLower hUpper F hF)
    (actualPlusCharge F) (fun r hr => (hc r hr).1.differentiableAt)
    (fun r hr => (hc r hr).2.1.differentiableAt) hq.1
  have h0 : InWeightedL2 sigma (fun _ => 0) := by simp [InWeightedL2]
  have ha := actualPlusCharge_difference_le sigma (by linarith) F (fun _ => 0) hF h0
  have hz : actualPlusCharge (fun _ => 0) = 0 := by simp [actualPlusCharge, channelPairing]
  rw [hz, innerWeightedData_zero sigma h0, sub_zero, sub_zero, ← innerWeightedNorm_eq sigma F hF] at ha
  refine ⟨hb.1, ?_⟩
  calc
    _ ≤ _ := hb.2
    _ ≤ innerPlusSecondDerivativeConstant sigma hLower hUpper * innerWeightedNorm sigma F +
        ((2 * ‖weightedSourceResonanceL2 sigma (by linarith)‖) * innerWeightedNorm sigma F) * innerWeightedNorm sigma affineModelSecondDerivative :=
      _root_.add_le_add hq.2 (mul_le_mul_of_nonneg_right ha (innerWeightedNorm_nonneg _ _))
    _ = _ := by unfold innerPlusOutputSecondConstant; ring
end HBL.Modulation.Monopole
