import HBL.InnerEstimates.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerWeightedNorm_nonneg (sigma : ℝ) (F : ℝ → ℝ) : 0 ≤ innerWeightedNorm sigma F :=
  ENNReal.toReal_nonneg
end HBL.Modulation.Monopole
