import HBL.InnerEstimates.MinusRemainderDifference
import HBL.InnerEstimates.MinusRemainderProperties
import HBL.InnerEstimates.BoundedWeightedNorm
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusRemainder_weighted_difference_le
    (sigma tau : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) (htau : 1 / 2 < tau)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) :
    innerWeightedNorm (-tau) (fun r => normalizedMinusRemainder sigma hLower hUpper F hF r -
        normalizedMinusRemainder sigma hLower hUpper G hG r) ≤
      (innerDecayNorm tau htau * innerMinusRemainderConstant sigma hLower hUpper) *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  have h := innerWeightedNorm_le_of_bound tau htau _
    ((normalizedMinusRemainder_properties sigma hLower hUpper F hF).1.sub
      (normalizedMinusRemainder_properties sigma hLower hUpper G hG).1) _
    (fun r hr => normalizedMinusRemainder_difference_le sigma hLower hUpper F G hF hG hr)
  exact h.trans_eq (by ring)
end HBL.Modulation.Monopole
