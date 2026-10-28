import HBL.InnerEstimates.MinusRemainderProperties
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusOutput_properties (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    InnerAffineProperties (normalizedMinusOutput sigma hLower hUpper F hF) (actualMinusCharge F) :=
  affineRestore_properties _ _ (normalizedMinusRemainder_properties sigma hLower hUpper F hF)
end HBL.Modulation.Monopole
