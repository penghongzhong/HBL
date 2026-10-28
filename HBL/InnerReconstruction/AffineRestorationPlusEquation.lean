import HBL.InnerReconstruction.AffineRestorationSecondDerivative
import HBL.InnerReconstruction.AffineRestorationNonlocal
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace ContDiff
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem affineRestore_hPlus (q : ℝ → ℝ) (a : ℝ)
    (hq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ q r)
    (hdq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv q) r)
    (hm : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure)
    {r : ℝ} (hr : 0 < r) :
    hPlusApply (affineRestore q a) r = hPlusApply q r + a * hPlusApply model r := by
  unfold hPlusApply
  rw [(affineRestore_second_hasDerivAt q a hq hdq hr).deriv, affineRestore_nonlocal q a hm hr.le]
  unfold affineRestore
  ring
end HBL.Modulation.Monopole
