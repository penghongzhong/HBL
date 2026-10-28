import HBL.InnerDerivatives.TailMomentBound
import HBL.InnerDerivatives.TotalSourceNorm
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerGreenDerivative_bound (g : RealL2 halfLineMeasure)
    (sigma : ℝ) (hsigma : 3 / 2 < sigma) (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    {r : ℝ} (hr : 0 < r) :
    (1 + r) * ‖innerGreenDerivative g F r‖ ≤
      innerGreenDerivativeMajorant * ‖g‖ + innerSourceDerivativeMajorant sigma hsigma * innerWeightedNorm sigma F := by
  have h := inner_totalSource_integral_norm_le g sigma hsigma F hF
  exact (halfLineGreenTail_moment_bound _ h.1 h.2.1 hr).trans h.2.2
end HBL.Modulation.Monopole
