import HBL.InnerReconstruction.SourceOperatorRepresentative
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem innerGreenRepresentative_ae_of_equation
    (x g : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (heq : x = weightedFreeGreenOperator g +
      weightedSourceGreenOperator sigma hsigma (weightedSourceDataL2 sigma F hF)) :
    (x : ℝ → ℝ) =ᵐ[halfLineMeasure]
      fun r => weightedGreenDecay r * innerGreenRepresentative g F r := by
  have hfun := congrArg (fun z : RealL2 halfLineMeasure => (z : ℝ → ℝ)) heq
  have hxAE : (x : ℝ → ℝ) =ᵐ[halfLineMeasure]
      ((weightedFreeGreenOperator g +
        weightedSourceGreenOperator sigma hsigma (weightedSourceDataL2 sigma F hF) : RealL2 halfLineMeasure) : ℝ → ℝ) :=
    Filter.Eventually.of_forall (fun r => congrFun hfun r)
  have hpoint := hxAE.trans
    (Lp.coeFn_add (weightedFreeGreenOperator g)
      (weightedSourceGreenOperator sigma hsigma (weightedSourceDataL2 sigma F hF)))
  filter_upwards [hpoint, weightedFreeGreenOperator_ae_pointwise g,
    weightedSourceGreenOperator_ae_primitive sigma hsigma F hF] with r hx hg hsource
  simp only [Pi.add_apply] at hx
  rw [hx, hg, hsource]
  unfold weightedFreeGreenPointwise innerGreenRepresentative
  ring
end HBL.Modulation.Monopole
