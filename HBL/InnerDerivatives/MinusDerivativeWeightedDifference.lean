import HBL.InnerDerivatives.MinusDerivativeWeighted
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusRemainder_derivative_weighted_difference
    (sigma beta : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) (hbeta : beta < 1 / 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G)
    (hcF : Continuous F) (hcG : Continuous G) :
    InWeightedL2 beta (fun r => deriv (normalizedMinusRemainder sigma hLower hUpper F hF) r -
      deriv (normalizedMinusRemainder sigma hLower hUpper G hG) r) ∧
    innerWeightedNorm beta (fun r => deriv (normalizedMinusRemainder sigma hLower hUpper F hF) r -
      deriv (normalizedMinusRemainder sigma hLower hUpper G hG) r) ≤
      innerDecayNorm (1 - beta) (by linarith) * innerMinusDerivativeConstant sigma hLower hUpper *
        innerWeightedNorm sigma (fun r => F r - G r) := by
  rw [innerWeightedNorm_sub_eq sigma F G hF hG]
  simpa only [mul_assoc] using innerWeightedNorm_le_of_inverse_linear_bound beta hbeta
    (fun r => deriv (normalizedMinusRemainder sigma hLower hUpper F hF) r -
      deriv (normalizedMinusRemainder sigma hLower hUpper G hG) r)
    ((aestronglyMeasurable_deriv _ _).sub (aestronglyMeasurable_deriv _ _))
    (innerMinusDerivativeConstant sigma hLower hUpper * ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖)
    (fun r hr => normalizedMinusRemainder_derivative_difference_le sigma hLower hUpper F G hF hG hcF hcG hr)
end HBL.Modulation.Monopole
