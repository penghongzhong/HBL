import HBL.InnerEstimates.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusInner_equation (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    (1 - weightedBirmanSchwingerOperator) (normalizedPlusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure) =
      weightedSourceGreenOperator sigma (by linarith) (correctedPlusDataL2 sigma hUpper.le F hF) :=
  weightedSourceFredholmSolution_equation sigma (by linarith) _ _ _
end HBL.Modulation.Monopole
