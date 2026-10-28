import HBL.InnerDerivatives.SecondSourceDifference
import HBL.InnerDerivatives.PlusSecondIdentity
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusRemainder_second_derivative_difference
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G)
    (hcF : Continuous F) (hcG : Continuous G) :
    InWeightedL2 sigma (fun r => deriv (deriv (normalizedPlusRemainder sigma hLower hUpper F hF)) r -
      deriv (deriv (normalizedPlusRemainder sigma hLower hUpper G hG)) r) ∧
    innerWeightedNorm sigma (fun r => deriv (deriv (normalizedPlusRemainder sigma hLower hUpper F hF)) r -
      deriv (deriv (normalizedPlusRemainder sigma hLower hUpper G hG)) r) ≤
      innerPlusSecondDerivativeConstant sigma hLower hUpper * innerWeightedNorm sigma (fun r => F r - G r) := by
  have hb := inner_second_source_difference_le sigma hUpper.le (weightedPotentialOperator (normalizedPlusInner sigma hLower hUpper F hF)) (weightedPotentialOperator (normalizedPlusInner sigma hLower hUpper G hG))
    (correctedPlusSource F) (correctedPlusSource G)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le G hG) _ _
    (normalizedPlusRemainder_second_derivative_ae sigma hLower hUpper F hF hcF)
    (normalizedPlusRemainder_second_derivative_ae sigma hLower hUpper G hG hcG)
  have hx := normalizedPlusInner_difference_le sigma hLower hUpper F G hF hG
  have hc := correctedPlusDataL2_difference_le sigma (by linarith) hUpper.le F G hF hG
  have hg : ‖(weightedPotentialOperator (normalizedPlusInner sigma hLower hUpper F hF)) - (weightedPotentialOperator (normalizedPlusInner sigma hLower hUpper G hG))‖ ≤ ‖weightedPotentialOperator‖ * (innerPlusHilbertConstant sigma hLower hUpper *
      ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖) := by
    have hv := weightedPotentialOperator.le_opNorm
      ((normalizedPlusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure) -
        (normalizedPlusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure))
    rw [map_sub] at hv
    exact hv.trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  refine ⟨hb.1, ?_⟩
  rw [innerWeightedNorm_sub_eq sigma F G hF hG]
  calc
    _ ≤ _ := hb.2
    _ ≤ _ := _root_.add_le_add hg hc
    _ = _ := by unfold innerPlusSecondDerivativeConstant innerPlusCorrectionConstant; ring
end HBL.Modulation.Monopole
