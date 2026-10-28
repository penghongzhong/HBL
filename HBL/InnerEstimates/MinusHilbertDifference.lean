import HBL.InnerEstimates.FredholmDifference
import HBL.InnerEstimates.MinusEquation
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusInner_difference_le
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) :
    ‖(normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure) -
        (normalizedMinusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure)‖ ≤
      innerMinusHilbertConstant sigma hLower hUpper *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  have h := innerFredholm_norm_sub_le weightedPhaseBirman weightedPhaseBirman_compact
    (normalizedMinusInner sigma hLower hUpper F hF)
    (normalizedMinusInner sigma hLower hUpper G hG)
  rw [normalizedMinusInner_equation, normalizedMinusInner_equation, ← map_sub] at h
  have hc := correctedMinusDataL2_difference_le sigma (by linarith) hUpper.le F G hF hG
  have hB := (weightedSourceGreenOperator sigma (by linarith)).le_opNorm
    (correctedMinusDataL2 sigma hUpper.le F hF - correctedMinusDataL2 sigma hUpper.le G hG)
  calc
    _ ≤ _ := h
    _ ≤ (innerFredholmConstant weightedPhaseBirman weightedPhaseBirman_compact : ℝ) *
        (‖weightedSourceGreenOperator sigma (by linarith)‖ *
          (innerMinusCorrectionConstant sigma hLower hUpper *
            ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hB.trans (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
    _ = _ := by unfold innerMinusHilbertConstant; ring
end HBL.Modulation.Monopole
