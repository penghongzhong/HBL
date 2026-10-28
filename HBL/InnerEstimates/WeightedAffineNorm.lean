import HBL.InnerEstimates.WeightedNormIdentity
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerWeighted_sub_const_mul_bound (sigma : ℝ) (F G : ℝ → ℝ)
    (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ) :
    InWeightedL2 sigma (fun r => F r - a * G r) ∧
    innerWeightedNorm sigma (fun r => F r - a * G r) ≤
      innerWeightedNorm sigma F + ‖a‖ * innerWeightedNorm sigma G := by
  have hH : InWeightedL2 sigma (fun r => F r - a * G r) := by
    unfold InWeightedL2 at *
    convert hF.sub (hG.const_mul a) using 1
    funext r
    simp only [Pi.sub_apply]
    ring
  refine ⟨hH, ?_⟩
  rw [innerWeightedNorm_eq sigma _ hH, weightedSourceDataL2_sub_const_mul,
    innerWeightedNorm_eq sigma F hF, innerWeightedNorm_eq sigma G hG]
  simpa only [norm_smul] using norm_sub_le (weightedSourceDataL2 sigma F hF)
    (a • weightedSourceDataL2 sigma G hG)
end HBL.Modulation.Monopole
