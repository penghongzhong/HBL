import HBL.InnerDerivatives.PlusSecondDifference
import HBL.InnerDerivatives.RemainderZero
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusRemainder_second_derivative_bound
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F) :
    InWeightedL2 sigma (deriv (deriv (normalizedPlusRemainder sigma hLower hUpper F hF))) ∧
    innerWeightedNorm sigma (deriv (deriv (normalizedPlusRemainder sigma hLower hUpper F hF))) ≤
      innerPlusSecondDerivativeConstant sigma hLower hUpper * innerWeightedNorm sigma F := by
  have h0 : InWeightedL2 sigma (fun _ => 0) := by simp [InWeightedL2]
  have hb := normalizedPlusRemainder_second_derivative_difference sigma hLower hUpper F (fun _ => 0) hF h0 hcF continuous_const
  rw [(normalizedRemainder_zero sigma hLower hUpper h0).1] at hb
  have hz : deriv (fun _ : ℝ => (0 : ℝ)) = (fun _ => 0) := funext (fun r => deriv_const r 0)
  simpa only [hz, deriv_const, sub_zero] using hb
end HBL.Modulation.Monopole
