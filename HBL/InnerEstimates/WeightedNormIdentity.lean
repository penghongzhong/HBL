import HBL.InnerEstimates.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerWeightedNorm_eq (sigma : ℝ) (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    innerWeightedNorm sigma F = ‖weightedSourceDataL2 sigma F hF‖ := by
  exact (Lp.norm_toLp _ hF).symm
end HBL.Modulation.Monopole
