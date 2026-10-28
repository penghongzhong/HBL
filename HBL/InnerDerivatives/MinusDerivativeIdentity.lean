import HBL.InnerDerivatives.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusRemainder_hasDerivAt
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (normalizedMinusRemainder sigma hLower hUpper F hF)
      (innerGreenDerivative ((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure)) (correctedMinusSource F) r) r := by
  let x : RealL2 halfLineMeasure := normalizedMinusInner sigma hLower hUpper F hF
  let q := normalizedMinusRemainder sigma hLower hUpper F hF
  have hx := phase_innerGreenRepresentative_ae x sigma (by linarith) (correctedMinusSource F)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF)
    (normalizedMinusInner_equation sigma hLower hUpper F hF)
  have hc := phase_innerGreenRepresentative_classical x sigma (by linarith) (correctedMinusSource F)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF) (correctedMinusSource_continuous F hcF)
    (normalizedMinusInner_equation sigma hLower hUpper F hF)
  have hsource : (fun t => weightedGreenDecay t * (((3 : ℝ) • x) : RealL2 halfLineMeasure) t + correctedMinusSource F t)
      =ᵐ[halfLineMeasure] reconstructedPhaseSource q (correctedMinusSource F) := by
    filter_upwards [phase_reconstructed_source_ae x q hx] with t ht
    rw [ht]
    unfold reconstructedPhaseSource
    ring
  have he : innerGreenDerivative ((3 : ℝ) • x) (correctedMinusSource F) r =
      halfLineGreenTail (reconstructedPhaseSource q (correctedMinusSource F)) r := by
    apply integral_congr_ae
    exact hsource.filter_mono (ae_mono (Measure.restrict_mono (Ioi_subset_Ioi hr.le) le_rfl))
  change HasDerivAt q (innerGreenDerivative ((3 : ℝ) • x) (correctedMinusSource F) r) r
  rw [he]
  exact (hc r hr).1
end HBL.Modulation.Monopole
