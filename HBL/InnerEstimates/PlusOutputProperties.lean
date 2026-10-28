import HBL.InnerEstimates.PlusRemainderProperties
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusOutput_properties (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    InnerAffineProperties (normalizedPlusOutput sigma hLower hUpper F hF) (actualPlusCharge F) :=
  affineRestore_properties _ _ (normalizedPlusRemainder_properties sigma hLower hUpper F hF)
end HBL.Modulation.Monopole
