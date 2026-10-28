import HBL.InnerDerivatives.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem affineRestore_deriv_far (q : ℝ → ℝ) (a : ℝ) {r : ℝ} (hr : 2 < r)
    (hq : DifferentiableAt ℝ q r) :
    deriv (affineRestore q a) r = deriv q r + a := by
  have h := (hq.hasDerivAt.add ((model_hasDerivAt_one_of_two_lt r hr).const_mul a)).deriv
  have he : affineRestore q a = q + fun t => a * model t := by funext t; rfl
  rw [he]
  simpa only [mul_one] using h
end HBL.Modulation.Monopole
