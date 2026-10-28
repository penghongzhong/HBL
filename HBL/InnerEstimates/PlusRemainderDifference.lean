import HBL.InnerEstimates.PlusHilbertDifference
import HBL.InnerEstimates.RepresentativeDifferenceBound
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusRemainder_difference_le
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G)
    {r : ℝ} (hr : 0 < r) :
    ‖normalizedPlusRemainder sigma hLower hUpper F hF r -
        normalizedPlusRemainder sigma hLower hUpper G hG r‖ ≤
      innerPlusRemainderConstant sigma hLower hUpper *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  have h := innerGreenRepresentative_difference_le (weightedPotentialOperator (normalizedPlusInner sigma hLower hUpper F hF)) (weightedPotentialOperator (normalizedPlusInner sigma hLower hUpper G hG)) sigma hLower
    (correctedPlusSource F) (correctedPlusSource G)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le G hG) hr
  have hx := normalizedPlusInner_difference_le sigma hLower hUpper F G hF hG
  have hc := correctedPlusDataL2_difference_le sigma (by linarith) hUpper.le F G hF hG
  have hv := weightedPotentialOperator.le_opNorm
    ((normalizedPlusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure) -
      (normalizedPlusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure))
  rw [map_sub] at hv
  calc
    _ ≤ _ := h
    _ ≤ innerGreenMajorantNorm * (‖weightedPotentialOperator‖ * (innerPlusHilbertConstant sigma hLower hUpper *
          ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖)) +
        innerMomentNorm sigma hLower * (innerPlusCorrectionConstant sigma hLower hUpper *
          ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by unfold innerGreenMajorantNorm; positivity)
        exact hv.trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
      · exact mul_le_mul_of_nonneg_left hc (by unfold innerMomentNorm; positivity)
    _ = _ := by unfold innerPlusRemainderConstant; ring
end HBL.Modulation.Monopole
