import HBL.InnerReconstruction.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem halfLineMinGreen_kernel_integrable
    (F : ℝ → ℝ) (hF : Integrable F halfLineMeasure) (r : ℝ) :
    Integrable (fun rho : ℝ => min r rho * F rho) halfLineMeasure := by
  refine (hF.norm.const_mul |r|).mono' ?_ ?_
  · exact (continuous_const.min continuous_id).aestronglyMeasurable.mul hF.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    rw [norm_mul, Real.norm_eq_abs (min r rho)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    by_cases h : r ≤ rho
    · rw [min_eq_left h]
    · have h' := lt_of_not_ge h
      rw [min_eq_right h'.le, abs_of_pos hrho, abs_of_pos (hrho.trans h')]
      exact h'.le
end HBL.Modulation.Monopole
