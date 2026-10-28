import HBL.InnerEstimates.MinusHilbertDifference
import HBL.InnerDerivatives.GreenDerivativeDifference
import HBL.InnerDerivatives.MinusDerivativeIdentity
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusRemainder_derivative_difference_le
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G)
    (hcF : Continuous F) (hcG : Continuous G)
    {r : ℝ} (hr : 0 < r) :
    (1 + r) * ‖deriv (normalizedMinusRemainder sigma hLower hUpper F hF) r -
        deriv (normalizedMinusRemainder sigma hLower hUpper G hG) r‖ ≤
      innerMinusDerivativeConstant sigma hLower hUpper *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  rw [(normalizedMinusRemainder_hasDerivAt sigma hLower hUpper F hF hcF hr).deriv,
    (normalizedMinusRemainder_hasDerivAt sigma hLower hUpper G hG hcG hr).deriv]
  have h := innerGreenDerivative_difference_le (((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure))) (((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure))) sigma hLower
    (correctedMinusSource F) (correctedMinusSource G)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le G hG) hr
  have hx := normalizedMinusInner_difference_le sigma hLower hUpper F G hF hG
  have hc := correctedMinusDataL2_difference_le sigma (by linarith) hUpper.le F G hF hG

  calc
    _ ≤ _ := h
    _ ≤ innerGreenDerivativeMajorant * (3 * (innerMinusHilbertConstant sigma hLower hUpper *
          ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖)) +
        innerSourceDerivativeMajorant sigma hLower * (innerMinusCorrectionConstant sigma hLower hUpper *
          ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by unfold innerGreenDerivativeMajorant innerGreenMajorantNorm; positivity)
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
        exact mul_le_mul_of_nonneg_left hx (by norm_num)
      · exact mul_le_mul_of_nonneg_left hc (by unfold innerSourceDerivativeMajorant innerDecayNorm innerMomentNorm; positivity)
    _ = _ := by unfold innerMinusDerivativeConstant; ring
end HBL.Modulation.Monopole
