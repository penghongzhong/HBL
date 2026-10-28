import HBL.InnerReconstruction.OperatorRepresentative
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem plus_innerGreenRepresentative_ae
    (x : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (heq : (1 - weightedBirmanSchwingerOperator) x =
      weightedSourceGreenOperator sigma hsigma (weightedSourceDataL2 sigma F hF)) :
    (x : ℝ → ℝ) =ᵐ[halfLineMeasure]
      fun r => weightedGreenDecay r *
        innerGreenRepresentative (weightedPotentialOperator x) F r := by
  apply innerGreenRepresentative_ae_of_equation x _ sigma hsigma F hF
  change x - weightedFreeGreenOperator (weightedPotentialOperator x) =
    weightedSourceGreenOperator sigma hsigma (weightedSourceDataL2 sigma F hF) at heq
  have h := (sub_eq_iff_eq_add).mp heq
  simpa only [add_comm] using h
end HBL.Modulation.Monopole
