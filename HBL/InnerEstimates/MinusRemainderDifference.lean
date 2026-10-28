import HBL.InnerEstimates.MinusHilbertDifference
import HBL.InnerEstimates.RepresentativeDifferenceBound
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusRemainder_difference_le
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G)
    {r : ℝ} (hr : 0 < r) :
    ‖normalizedMinusRemainder sigma hLower hUpper F hF r -
        normalizedMinusRemainder sigma hLower hUpper G hG r‖ ≤
      innerMinusRemainderConstant sigma hLower hUpper *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  have h := innerGreenRepresentative_difference_le (((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure))) (((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure))) sigma hLower
    (correctedMinusSource F) (correctedMinusSource G)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le G hG) hr
  have hx := normalizedMinusInner_difference_le sigma hLower hUpper F G hF hG
  have hc := correctedMinusDataL2_difference_le sigma (by linarith) hUpper.le F G hF hG

  calc
    _ ≤ _ := h
    _ ≤ innerGreenMajorantNorm * (3 * (innerMinusHilbertConstant sigma hLower hUpper *
          ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖)) +
        innerMomentNorm sigma hLower * (innerMinusCorrectionConstant sigma hLower hUpper *
          ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by unfold innerGreenMajorantNorm; positivity)
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
        exact mul_le_mul_of_nonneg_left hx (by norm_num)
      · exact mul_le_mul_of_nonneg_left hc (by unfold innerMomentNorm; positivity)
    _ = _ := by unfold innerMinusRemainderConstant; ring
end HBL.Modulation.Monopole
