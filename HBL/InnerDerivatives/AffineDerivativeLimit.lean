import HBL.InnerDerivatives.AffineDerivativeFar
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem affineRestore_derivative_limit (q : ℝ → ℝ) (a : ℝ)
    (g : RealL2 halfLineMeasure) (F : ℝ → ℝ)
    (hq : ∀ r : ℝ, 0 < r → HasDerivAt q (innerGreenDerivative g F r) r) :
    Tendsto (deriv (affineRestore q a)) atTop (𝓝 a) := by
  have ht : Tendsto (innerGreenDerivative g F) atTop (𝓝 (0 : ℝ)) :=
    tendsto_integral_Ioi_zero tendsto_id
  have he : deriv (affineRestore q a) =ᶠ[atTop] (fun r => innerGreenDerivative g F r + a) := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with r hr
    rw [affineRestore_deriv_far q a hr (hq r (by linarith)).differentiableAt,
      (hq r (by linarith)).deriv]
  exact (tendsto_congr' he).2 (by simpa only [zero_add] using ht.add_const a)
end HBL.Modulation.Monopole
