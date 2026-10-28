import HBL.InnerDerivatives.MinusDerivativeDifference
import HBL.InnerDerivatives.RemainderZero
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedMinusRemainder_derivative_bound
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) {r : ℝ} (hr : 0 < r) :
    (1 + r) * ‖deriv (normalizedMinusRemainder sigma hLower hUpper F hF) r‖ ≤
      innerMinusDerivativeConstant sigma hLower hUpper * innerWeightedNorm sigma F := by
  have h0 : InWeightedL2 sigma (fun _ => 0) := by
    simp [InWeightedL2]
  have h := normalizedMinusRemainder_derivative_difference_le sigma hLower hUpper F (fun _ => 0)
    hF h0 hcF continuous_const hr
  rw [(normalizedRemainder_zero sigma hLower hUpper h0).2, innerWeightedData_zero sigma h0] at h
  simpa only [deriv_const, sub_zero, ← innerWeightedNorm_eq sigma F hF] using h
end HBL.Modulation.Monopole
