import HBL.InnerEstimates.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusRemainder_properties (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    InnerRemainderProperties (normalizedPlusRemainder sigma hLower hUpper F hF) :=
  innerGreenRepresentative_properties _ sigma hLower _
    (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF)
end HBL.Modulation.Monopole
