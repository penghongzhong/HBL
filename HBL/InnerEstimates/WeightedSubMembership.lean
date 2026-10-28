import HBL.InnerEstimates.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerWeighted_sub_mem (sigma : ℝ) (F G : ℝ → ℝ)
    (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) :
    InWeightedL2 sigma (fun r => F r - G r) := by
  unfold InWeightedL2 at *
  convert hF.sub hG using 1
  funext r
  simp only [Pi.sub_apply]
  ring
end HBL.Modulation.Monopole
