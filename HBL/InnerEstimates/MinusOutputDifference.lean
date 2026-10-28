import HBL.InnerEstimates.MinusRemainderWeightedDifference
import HBL.InnerEstimates.AffineWeightedDifference
import HBL.InnerEstimates.WeightedNormNonnegative
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

def innerMinusOutputConstant (sigma tau : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (htau : 3 / 2 < tau) : ℝ :=
  innerDecayNorm tau (by linarith) * innerMinusRemainderConstant sigma hLower hUpper +
    (‖weightedPhaseSourceResonanceL2 sigma (by linarith)‖) * innerWeightedNorm (-tau) model

theorem normalizedMinusOutput_weighted_difference_le
    (sigma tau : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) (htau : 3 / 2 < tau)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) :
    innerWeightedNorm (-tau) (fun r => normalizedMinusOutput sigma hLower hUpper F hF r -
        normalizedMinusOutput sigma hLower hUpper G hG r) ≤
      innerMinusOutputConstant sigma tau hLower hUpper htau *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  have h := (affineRestore_weighted_difference_bound tau htau _ _
    (normalizedMinusRemainder_properties sigma hLower hUpper F hF).1
    (normalizedMinusRemainder_properties sigma hLower hUpper G hG).1
    (actualMinusCharge F) (actualMinusCharge G) _
    (fun r hr => normalizedMinusRemainder_difference_le sigma hLower hUpper F G hF hG hr)).2
  have ha := actualMinusCharge_difference_le sigma (by linarith) F G hF hG
  calc
    _ ≤ _ := h
    _ ≤ innerDecayNorm tau (by linarith) *
        (innerMinusRemainderConstant sigma hLower hUpper *
          ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖) +
        ((‖weightedPhaseSourceResonanceL2 sigma (by linarith)‖) * ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖) *
          innerWeightedNorm (-tau) model := by
      exact _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_right ha (innerWeightedNorm_nonneg _ _))
    _ = _ := by unfold innerMinusOutputConstant; ring
end HBL.Modulation.Monopole
