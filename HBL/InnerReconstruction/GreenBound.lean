import HBL.InnerReconstruction.GreenKernelIntegrable
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem halfLineMinGreen_abs_le_firstMoment
    (F : ℝ → ℝ) (hF : Integrable F halfLineMeasure)
    (hM : Integrable (fun rho : ℝ => rho * F rho) halfLineMeasure)
    {r : ℝ} (hr : 0 ≤ r) :
    |halfLineMinGreen F r| ≤ ∫ rho, ‖rho * F rho‖ ∂halfLineMeasure := by
  unfold halfLineMinGreen
  change |∫ rho, min r rho * F rho ∂halfLineMeasure| ≤ _
  calc
    _ ≤ ∫ rho, ‖min r rho * F rho‖ ∂halfLineMeasure := abs_integral_le_integral_abs
    _ ≤ _ := by
      apply integral_mono_ae (halfLineMinGreen_kernel_integrable F hF r).norm hM.norm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
      rw [norm_mul, norm_mul, Real.norm_eq_abs (min r rho), Real.norm_eq_abs rho,
        abs_of_nonneg (le_min hr hrho.le), abs_of_pos hrho]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
end HBL.Modulation.Monopole
