import HBL.InnerDerivatives.MinusDerivativeBound
import HBL.InnerDerivatives.AffineDerivativeLimit
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusOutput_derivative_tail
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) :
    (∀ r : ℝ, 2 < r →
      (1 + r) * ‖deriv (normalizedMinusOutput sigma hLower hUpper F hF) r - actualMinusCharge F‖ ≤
        innerMinusDerivativeConstant sigma hLower hUpper * innerWeightedNorm sigma F) ∧
    Tendsto (deriv (normalizedMinusOutput sigma hLower hUpper F hF)) atTop (𝓝 (actualMinusCharge F)) := by
  have hq := fun r hr => normalizedMinusRemainder_hasDerivAt sigma hLower hUpper F hF hcF (r := r) hr
  constructor
  · intro r hr
    change (1 + r) * ‖deriv (affineRestore (normalizedMinusRemainder sigma hLower hUpper F hF) (actualMinusCharge F)) r - actualMinusCharge F‖ ≤ _
    rw [affineRestore_deriv_far _ _ hr (hq r (by linarith)).differentiableAt, add_sub_cancel_right]
    exact normalizedMinusRemainder_derivative_bound sigma hLower hUpper F hF hcF (by linarith)
  · exact affineRestore_derivative_limit _ _ ((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure)) (correctedMinusSource F) hq
end HBL.Modulation.Monopole
