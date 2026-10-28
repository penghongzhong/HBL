import HBL.InnerReconstruction.AffineRestorationDefinitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace ContDiff
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem affineRestore_second_hasDerivAt (q : ℝ → ℝ) (a : ℝ)
    (hq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ q r)
    (hdq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv q) r)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (affineRestore q a))
      (deriv (deriv q) r + a * deriv (deriv model) r) r := by
  have hm : Differentiable ℝ model := (contDiff_infty_iff_deriv.mp model_contDiff_infty).1
  have hdm : Differentiable ℝ (deriv model) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp model_contDiff_infty).2).1
  have hdd := (hdq r hr).hasDerivAt.add ((hdm r).hasDerivAt.const_mul a)
  apply hdd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with t ht
  exact ((hq t ht).hasDerivAt.add ((hm t).hasDerivAt.const_mul a)).deriv
end HBL.Modulation.Monopole
