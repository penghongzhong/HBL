import HBL.InnerReconstruction.AffineRestorationSecondDerivative
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace ContDiff
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem affineRestore_hMinus (q : ℝ → ℝ) (a : ℝ)
    (hq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ q r)
    (hdq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv q) r)
    {r : ℝ} (hr : 0 < r) :
    hMinusApply (affineRestore q a) r = hMinusApply q r + a * hMinusApply model r := by
  unfold hMinusApply
  rw [(affineRestore_second_hasDerivAt q a hq hdq hr).deriv]
  unfold affineRestore
  ring
end HBL.Modulation.Monopole
