import HBL.InnerDerivatives.PlusDerivativeBound
import HBL.InnerDerivatives.WeightedDecayBound
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusRemainder_derivative_weighted
    (sigma beta : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) (hbeta : beta < 1 / 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) :
    InWeightedL2 beta (deriv (normalizedPlusRemainder sigma hLower hUpper F hF)) ∧
    innerWeightedNorm beta (deriv (normalizedPlusRemainder sigma hLower hUpper F hF)) ≤
      innerDecayNorm (1 - beta) (by linarith) * innerPlusDerivativeConstant sigma hLower hUpper * innerWeightedNorm sigma F := by
  simpa only [mul_assoc] using innerWeightedNorm_le_of_inverse_linear_bound beta hbeta
    (deriv (normalizedPlusRemainder sigma hLower hUpper F hF)) (aestronglyMeasurable_deriv _ _)
    (innerPlusDerivativeConstant sigma hLower hUpper * innerWeightedNorm sigma F)
    (fun r hr => normalizedPlusRemainder_derivative_bound sigma hLower hUpper F hF hcF hr)
end HBL.Modulation.Monopole
