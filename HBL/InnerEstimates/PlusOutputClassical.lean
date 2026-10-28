import HBL.InnerEstimates.PlusEquation
import HBL.InnerEstimates.PlusOutputProperties
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusOutput_classical
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) :
    ∀ r : ℝ, 0 < r →
      DifferentiableAt ℝ (normalizedPlusOutput sigma hLower hUpper F hF) r ∧
      DifferentiableAt ℝ (deriv (normalizedPlusOutput sigma hLower hUpper F hF)) r ∧
      hPlusApply (normalizedPlusOutput sigma hLower hUpper F hF) r = F r := by
  let q := normalizedPlusRemainder sigma hLower hUpper F hF
  have hc := plus_innerGreenRepresentative_classical
    (normalizedPlusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure)
    sigma (by linarith) (correctedPlusSource F)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF)
    (correctedPlusSource_continuous F hcF)
    (normalizedPlusInner_equation sigma hLower hUpper F hF)
  have hq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ q r := fun r hr => (hc r hr).1.differentiableAt
  have hdq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv q) r := fun r hr => (hc r hr).2.1.differentiableAt
  have hx := plus_innerGreenRepresentative_ae
    (normalizedPlusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure)
    sigma (by linarith) (correctedPlusSource F)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF)
    (normalizedPlusInner_equation sigma hLower hUpper F hF)
  have hmem : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure :=
    (Lp.memLp (normalizedPlusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure)).ae_eq hx
  intro r hr
  have hm := (contDiff_infty_iff_deriv.mp model_contDiff_infty).1 r
  refine ⟨(hq r hr).add (hm.const_mul _),
    (affineRestore_second_hasDerivAt q _ hq hdq hr).differentiableAt, ?_⟩
  change hPlusApply (affineRestore q (actualPlusCharge F)) r = F r
  have heq : hPlusApply q r = correctedPlusSource F r := (hc r hr).2.2
  rw [affineRestore_hPlus q _ hq hdq hmem hr, heq]
  change F r - actualPlusCharge F * hPlusApply model r + actualPlusCharge F * hPlusApply model r = F r
  ring
end HBL.Modulation.Monopole
