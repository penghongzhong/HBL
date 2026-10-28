import HBL.InnerEstimates.FredholmDifference
import HBL.InnerEstimates.PlusEquation
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusInner_difference_le
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) :
    ‖(normalizedPlusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure) -
        (normalizedPlusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure)‖ ≤
      innerPlusHilbertConstant sigma hLower hUpper *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  have h := innerFredholm_norm_sub_le weightedBirmanSchwingerOperator weightedBirmanSchwingerOperator_compact
    (normalizedPlusInner sigma hLower hUpper F hF)
    (normalizedPlusInner sigma hLower hUpper G hG)
  rw [normalizedPlusInner_equation, normalizedPlusInner_equation, ← map_sub] at h
  have hc := correctedPlusDataL2_difference_le sigma (by linarith) hUpper.le F G hF hG
  have hB := (weightedSourceGreenOperator sigma (by linarith)).le_opNorm
    (correctedPlusDataL2 sigma hUpper.le F hF - correctedPlusDataL2 sigma hUpper.le G hG)
  calc
    _ ≤ _ := h
    _ ≤ (innerFredholmConstant weightedBirmanSchwingerOperator weightedBirmanSchwingerOperator_compact : ℝ) *
        (‖weightedSourceGreenOperator sigma (by linarith)‖ *
          (innerPlusCorrectionConstant sigma hLower hUpper *
            ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hB.trans (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
    _ = _ := by unfold innerPlusHilbertConstant; ring
end HBL.Modulation.Monopole
