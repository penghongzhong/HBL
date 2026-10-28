import HBL.InnerReconstruction.GreenKernelIntegrable
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem halfLineMinGreen_lipschitz
    (F : ℝ → ℝ) (hF : Integrable F halfLineMeasure) :
    LipschitzWith (sourceGreenLipschitzConstant F) (halfLineMinGreen F) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  rw [Real.dist_eq]
  unfold halfLineMinGreen
  change |(∫ rho, min r rho * F rho ∂halfLineMeasure) -
      (∫ rho, min s rho * F rho ∂halfLineMeasure)| ≤ _
  have hr := halfLineMinGreen_kernel_integrable F hF r
  have hs := halfLineMinGreen_kernel_integrable F hF s
  rw [← integral_sub hr hs]
  calc
    _ ≤ ∫ rho, ‖min r rho * F rho - min s rho * F rho‖ ∂halfLineMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ rho, |r - s| * ‖F rho‖ ∂halfLineMeasure := by
      apply integral_mono_ae (hr.sub hs).norm (hF.norm.const_mul |r - s|)
      filter_upwards with rho
      simp only [Pi.sub_apply]
      rw [← sub_mul, norm_mul, Real.norm_eq_abs (min r rho - min s rho)]
      exact mul_le_mul_of_nonneg_right
        (abs_min_sub_min_le_max r rho s rho |>.trans_eq (by simp)) (norm_nonneg _)
    _ = ↑(sourceGreenLipschitzConstant F) * dist r s := by
      rw [integral_const_mul, Real.dist_eq]
      exact mul_comm _ _
end HBL.Modulation.Monopole
