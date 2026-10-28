import HBL.InnerEstimates.MinusEquation
import HBL.InnerEstimates.MinusOutputProperties
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusOutput_classical
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) :
    ∀ r : ℝ, 0 < r →
      DifferentiableAt ℝ (normalizedMinusOutput sigma hLower hUpper F hF) r ∧
      DifferentiableAt ℝ (deriv (normalizedMinusOutput sigma hLower hUpper F hF)) r ∧
      hMinusApply (normalizedMinusOutput sigma hLower hUpper F hF) r = F r := by
  let q := normalizedMinusRemainder sigma hLower hUpper F hF
  have hc := phase_innerGreenRepresentative_classical
    (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure)
    sigma (by linarith) (correctedMinusSource F)
    (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF)
    (correctedMinusSource_continuous F hcF)
    (normalizedMinusInner_equation sigma hLower hUpper F hF)
  have hq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ q r := fun r hr => (hc r hr).1.differentiableAt
  have hdq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv q) r := fun r hr => (hc r hr).2.1.differentiableAt
  intro r hr
  have hm := (contDiff_infty_iff_deriv.mp model_contDiff_infty).1 r
  refine ⟨(hq r hr).add (hm.const_mul _),
    (affineRestore_second_hasDerivAt q _ hq hdq hr).differentiableAt, ?_⟩
  change hMinusApply (affineRestore q (actualMinusCharge F)) r = F r
  have heq : hMinusApply q r = correctedMinusSource F r := (hc r hr).2.2
  rw [affineRestore_hMinus q _ hq hdq hr, heq]
  change F r - actualMinusCharge F * hMinusApply model r + actualMinusCharge F * hMinusApply model r = F r
  ring
end HBL.Modulation.Monopole
