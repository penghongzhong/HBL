import HBL.InnerReconstruction.GreenKernelIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem halfLineMinGreen_tendsto_firstMoment
    (F : ℝ → ℝ) (hF : Integrable F halfLineMeasure)
    (hM : Integrable (fun rho : ℝ => rho * F rho) halfLineMeasure) :
    Tendsto (halfLineMinGreen F) atTop
      (𝓝 (∫ rho, rho * F rho ∂halfLineMeasure)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun rho => ‖rho * F rho‖)
  · exact Filter.Eventually.of_forall fun r =>
      (halfLineMinGreen_kernel_integrable F hF r).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    rw [norm_mul, norm_mul, Real.norm_eq_abs (min r rho), Real.norm_eq_abs rho,
      abs_of_nonneg (le_min hr hrho.le), abs_of_pos hrho]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
  · exact hM.norm
  · filter_upwards with rho
    have heq : (fun r : ℝ => min r rho * F rho) =ᶠ[atTop]
        (fun _ : ℝ => rho * F rho) := by
      filter_upwards [eventually_ge_atTop rho] with r hr
      rw [min_eq_right hr]
    exact (tendsto_congr' heq).2 tendsto_const_nhds
end HBL.Modulation.Monopole
