import HBL.InnerDerivatives.SecondDefinitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusRemainder_second_derivative_ae
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) :
    deriv (deriv (normalizedMinusRemainder sigma hLower hUpper F hF)) =ᵐ[halfLineMeasure]
      (fun r => -(weightedGreenDecay r * ((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure) : RealL2 halfLineMeasure) r + correctedMinusSource F r)) := by
  let x : RealL2 halfLineMeasure := normalizedMinusInner sigma hLower hUpper F hF
  let q := normalizedMinusRemainder sigma hLower hUpper F hF
  have hx := phase_innerGreenRepresentative_ae x sigma (by linarith) (correctedMinusSource F)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF)
    (normalizedMinusInner_equation sigma hLower hUpper F hF)
  have hc := phase_innerGreenRepresentative_classical x sigma (by linarith) (correctedMinusSource F)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF) (correctedMinusSource_continuous F hcF)
    (normalizedMinusInner_equation sigma hLower hUpper F hF)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, phase_reconstructed_source_ae x q hx] with r hr hsource
  change deriv (deriv q) r = -(weightedGreenDecay r * ((3 : ℝ) • x : RealL2 halfLineMeasure) r + correctedMinusSource F r)
  have hderiv : deriv (deriv q) r = -reconstructedPhaseSource q (correctedMinusSource F) r := (hc r hr).2.1.deriv
  rw [hderiv, hsource]
  unfold reconstructedPhaseSource
  ring
end HBL.Modulation.Monopole
