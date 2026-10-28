import HBL.InnerDerivatives.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusRemainder_hasDerivAt
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (normalizedPlusRemainder sigma hLower hUpper F hF)
      (innerGreenDerivative (weightedPotentialOperator (normalizedPlusInner sigma hLower hUpper F hF)) (correctedPlusSource F) r) r := by
  let x : RealL2 halfLineMeasure := normalizedPlusInner sigma hLower hUpper F hF
  let q := normalizedPlusRemainder sigma hLower hUpper F hF
  have hx := plus_innerGreenRepresentative_ae x sigma (by linarith) (correctedPlusSource F)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF)
    (normalizedPlusInner_equation sigma hLower hUpper F hF)
  have hc := plus_innerGreenRepresentative_classical x sigma (by linarith) (correctedPlusSource F)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF) (correctedPlusSource_continuous F hcF)
    (normalizedPlusInner_equation sigma hLower hUpper F hF)
  have hsource : (fun t => weightedGreenDecay t * (weightedPotentialOperator x : RealL2 halfLineMeasure) t + correctedPlusSource F t)
      =ᵐ[halfLineMeasure] reconstructedPlusSource q (correctedPlusSource F) := by
    filter_upwards [plus_reconstructed_source_ae x q hx] with t ht
    rw [ht]
    unfold reconstructedPlusSource
    ring
  have he : innerGreenDerivative (weightedPotentialOperator x) (correctedPlusSource F) r =
      halfLineGreenTail (reconstructedPlusSource q (correctedPlusSource F)) r := by
    apply integral_congr_ae
    exact hsource.filter_mono (ae_mono (Measure.restrict_mono (Ioi_subset_Ioi hr.le) le_rfl))
  change HasDerivAt q (innerGreenDerivative (weightedPotentialOperator x) (correctedPlusSource F) r) r
  rw [he]
  exact (hc r hr).1
end HBL.Modulation.Monopole
