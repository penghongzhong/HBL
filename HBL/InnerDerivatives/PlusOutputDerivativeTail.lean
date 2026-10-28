import HBL.InnerDerivatives.PlusDerivativeBound
import HBL.InnerDerivatives.AffineDerivativeLimit
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusOutput_derivative_tail
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) :
    (∀ r : ℝ, 2 < r →
      (1 + r) * ‖deriv (normalizedPlusOutput sigma hLower hUpper F hF) r - actualPlusCharge F‖ ≤
        innerPlusDerivativeConstant sigma hLower hUpper * innerWeightedNorm sigma F) ∧
    Tendsto (deriv (normalizedPlusOutput sigma hLower hUpper F hF)) atTop (𝓝 (actualPlusCharge F)) := by
  have hq := fun r hr => normalizedPlusRemainder_hasDerivAt sigma hLower hUpper F hF hcF (r := r) hr
  constructor
  · intro r hr
    change (1 + r) * ‖deriv (affineRestore (normalizedPlusRemainder sigma hLower hUpper F hF) (actualPlusCharge F)) r - actualPlusCharge F‖ ≤ _
    rw [affineRestore_deriv_far _ _ hr (hq r (by linarith)).differentiableAt, add_sub_cancel_right]
    exact normalizedPlusRemainder_derivative_bound sigma hLower hUpper F hF hcF (by linarith)
  · exact affineRestore_derivative_limit _ _ (weightedPotentialOperator (normalizedPlusInner sigma hLower hUpper F hF)) (correctedPlusSource F) hq
end HBL.Modulation.Monopole
