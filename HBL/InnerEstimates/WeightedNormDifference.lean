import HBL.InnerEstimates.WeightedNormIdentity
import HBL.InnerEstimates.WeightedSubMembership
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerWeightedNorm_sub_eq (sigma : ℝ) (F G : ℝ → ℝ)
    (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) :
    innerWeightedNorm sigma (fun r => F r - G r) =
      ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  rw [innerWeightedNorm_eq sigma _ (innerWeighted_sub_mem sigma F G hF hG)]
  have h := weightedSourceDataL2_sub_const_mul sigma F G hF hG 1
    (by simpa only [one_mul] using innerWeighted_sub_mem sigma F G hF hG)
  simpa only [one_mul, one_smul] using congrArg norm h
end HBL.Modulation.Monopole
