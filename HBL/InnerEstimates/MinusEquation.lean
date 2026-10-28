import HBL.InnerEstimates.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusInner_equation (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    (1 - weightedPhaseBirman) (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure) =
      weightedSourceGreenOperator sigma (by linarith) (correctedMinusDataL2 sigma hUpper.le F hF) :=
  (Classical.choose_spec (existsUnique_phaseWeightedSourceFredholmSolve sigma (by linarith)
    (correctedMinusSource F) (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF)
    (actualMinusCharge_orthogonal sigma (by linarith) F hF).2)).1
end HBL.Modulation.Monopole
