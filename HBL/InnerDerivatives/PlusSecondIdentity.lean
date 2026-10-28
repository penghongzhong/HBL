import HBL.InnerDerivatives.SecondDefinitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusRemainder_second_derivative_ae
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) :
    deriv (deriv (normalizedPlusRemainder sigma hLower hUpper F hF)) =ᵐ[halfLineMeasure]
      (fun r => -(weightedGreenDecay r * (weightedPotentialOperator (normalizedPlusInner sigma hLower hUpper F hF) : RealL2 halfLineMeasure) r + correctedPlusSource F r)) := by
  let x : RealL2 halfLineMeasure := normalizedPlusInner sigma hLower hUpper F hF
  let q := normalizedPlusRemainder sigma hLower hUpper F hF
  have hx := plus_innerGreenRepresentative_ae x sigma (by linarith) (correctedPlusSource F)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF)
    (normalizedPlusInner_equation sigma hLower hUpper F hF)
  have hc := plus_innerGreenRepresentative_classical x sigma (by linarith) (correctedPlusSource F)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF) (correctedPlusSource_continuous F hcF)
    (normalizedPlusInner_equation sigma hLower hUpper F hF)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, plus_reconstructed_source_ae x q hx] with r hr hsource
  change deriv (deriv q) r = -(weightedGreenDecay r * (weightedPotentialOperator x : RealL2 halfLineMeasure) r + correctedPlusSource F r)
  have hderiv : deriv (deriv q) r = -reconstructedPlusSource q (correctedPlusSource F) r := (hc r hr).2.1.deriv
  rw [hderiv, hsource]
  unfold reconstructedPlusSource
  ring
end HBL.Modulation.Monopole
