import HBL.InnerDerivatives.MinusSecondBound
import HBL.InnerDerivatives.AffineSecondWeighted
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

def innerMinusOutputSecondConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  innerMinusSecondDerivativeConstant sigma hLower hUpper + (‖weightedPhaseSourceResonanceL2 sigma (by linarith)‖) * innerWeightedNorm sigma affineModelSecondDerivative

theorem normalizedMinusOutput_second_derivative_bound
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) :
    InWeightedL2 sigma (deriv (deriv (normalizedMinusOutput sigma hLower hUpper F hF))) ∧
    innerWeightedNorm sigma (deriv (deriv (normalizedMinusOutput sigma hLower hUpper F hF))) ≤
      innerMinusOutputSecondConstant sigma hLower hUpper * innerWeightedNorm sigma F := by
  have hc := phase_innerGreenRepresentative_classical
    (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure)
    sigma (by linarith) (correctedMinusSource F)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF) (correctedMinusSource_continuous F hcF)
    (normalizedMinusInner_equation sigma hLower hUpper F hF)
  have hq := normalizedMinusRemainder_second_derivative_bound sigma hLower hUpper F hF hcF
  have hb := affineRestore_second_weighted_bound sigma (normalizedMinusRemainder sigma hLower hUpper F hF)
    (actualMinusCharge F) (fun r hr => (hc r hr).1.differentiableAt)
    (fun r hr => (hc r hr).2.1.differentiableAt) hq.1
  have h0 : InWeightedL2 sigma (fun _ => 0) := by simp [InWeightedL2]
  have ha := actualMinusCharge_difference_le sigma (by linarith) F (fun _ => 0) hF h0
  have hz : actualMinusCharge (fun _ => 0) = 0 := by simp [actualMinusCharge, channelPairing]
  rw [hz, innerWeightedData_zero sigma h0, sub_zero, sub_zero, ← innerWeightedNorm_eq sigma F hF] at ha
  refine ⟨hb.1, ?_⟩
  calc
    _ ≤ _ := hb.2
    _ ≤ innerMinusSecondDerivativeConstant sigma hLower hUpper * innerWeightedNorm sigma F +
        ((‖weightedPhaseSourceResonanceL2 sigma (by linarith)‖) * innerWeightedNorm sigma F) * innerWeightedNorm sigma affineModelSecondDerivative :=
      _root_.add_le_add hq.2 (mul_le_mul_of_nonneg_right ha (innerWeightedNorm_nonneg _ _))
    _ = _ := by unfold innerMinusOutputSecondConstant; ring
end HBL.Modulation.Monopole
