import HBL.InnerDerivatives.SecondSourceDifference
import HBL.InnerDerivatives.MinusSecondIdentity
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusRemainder_second_derivative_difference
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G)
    (hcF : Continuous F) (hcG : Continuous G) :
    InWeightedL2 sigma (fun r => deriv (deriv (normalizedMinusRemainder sigma hLower hUpper F hF)) r -
      deriv (deriv (normalizedMinusRemainder sigma hLower hUpper G hG)) r) ∧
    innerWeightedNorm sigma (fun r => deriv (deriv (normalizedMinusRemainder sigma hLower hUpper F hF)) r -
      deriv (deriv (normalizedMinusRemainder sigma hLower hUpper G hG)) r) ≤
      innerMinusSecondDerivativeConstant sigma hLower hUpper * innerWeightedNorm sigma (fun r => F r - G r) := by
  have hb := inner_second_source_difference_le sigma hUpper.le ((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure)) ((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure))
    (correctedMinusSource F) (correctedMinusSource G)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le G hG) _ _
    (normalizedMinusRemainder_second_derivative_ae sigma hLower hUpper F hF hcF)
    (normalizedMinusRemainder_second_derivative_ae sigma hLower hUpper G hG hcG)
  have hx := normalizedMinusInner_difference_le sigma hLower hUpper F G hF hG
  have hc := correctedMinusDataL2_difference_le sigma (by linarith) hUpper.le F G hF hG
  have hg : ‖((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure)) - ((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure))‖ ≤ 3 * (innerMinusHilbertConstant sigma hLower hUpper *
      ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖) := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    exact mul_le_mul_of_nonneg_left hx (by norm_num)
  refine ⟨hb.1, ?_⟩
  rw [innerWeightedNorm_sub_eq sigma F G hF hG]
  calc
    _ ≤ _ := hb.2
    _ ≤ _ := _root_.add_le_add hg hc
    _ = _ := by unfold innerMinusSecondDerivativeConstant innerMinusCorrectionConstant; ring
end HBL.Modulation.Monopole
