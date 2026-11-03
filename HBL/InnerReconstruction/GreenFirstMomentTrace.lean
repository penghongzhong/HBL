import HBL.InnerReconstruction.GreenC1Integrable
import HBL.InnerReconstruction.GreenBound
import HBL.InnerReconstruction.AffineRestorationDefinitions
import Mathlib.Tactic

/-!
Exact first-moment cancellation for the actual half-line Green primitive.
For integrable H with integrable first moment, q-r*q' is the truncated
first moment. The physical affine-restored q/r value and derivative
therefore have bounds M/r and M/r^2. The forced affine charge is retained.
No uniform smallness of M, source continuity, interface compatibility,
concentration-time law or nonlinear profile theorem is assumed here.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The genuine absolute first moment of the same Green source. -/
def halfLineGreenAbsoluteFirstMoment (H : ℝ → ℝ) : ℝ :=
  ∫ rho, ‖rho * H rho‖ ∂halfLineMeasure

/-- Exact cancellation, valid for merely integrable forcing. -/
theorem halfLineMinGreen_sub_radius_slope_eq_firstMoment
    (H : ℝ → ℝ) (hH : Integrable H halfLineMeasure) (r : ℝ) :
    halfLineMinGreen H r - r * halfLineL1GreenSlope H r =
      ∫ rho, (Iic r).indicator (fun t : ℝ => t * H t) rho
        ∂halfLineMeasure := by
  have hTail := hH.indicator measurableSet_Ioi
  change (∫ rho, min r rho * H rho ∂halfLineMeasure) -
    r * (∫ rho, (Ioi r).indicator H rho ∂halfLineMeasure) = _
  rw [← integral_const_mul,
    ← integral_sub (halfLineMinGreen_kernel_integrable H hH r)
      (hTail.const_mul r)]
  apply integral_congr_ae
  filter_upwards with rho
  by_cases hle : rho ≤ r
  · rw [min_eq_right hle,
      indicator_of_notMem (show rho ∉ Ioi r from not_lt.mpr hle),
      indicator_of_mem (show rho ∈ Iic r from hle)]
    ring
  · have hlt : r < rho := lt_of_not_ge hle
    rw [min_eq_left hlt.le,
      indicator_of_mem (show rho ∈ Ioi r from hlt),
      indicator_of_notMem (show rho ∉ Iic r from hle)]
    ring

/-- Both the Green value and its cancellation with r times its slope
are controlled by the same actual first moment. -/
theorem halfLineMinGreen_firstMoment_bounds
    (H : ℝ → ℝ) (hH : Integrable H halfLineMeasure)
    (hM : Integrable (fun rho : ℝ => rho * H rho) halfLineMeasure)
    (r : ℝ) (hr : 0 ≤ r) :
    |halfLineMinGreen H r| ≤ halfLineGreenAbsoluteFirstMoment H ∧
    |halfLineMinGreen H r - r * halfLineL1GreenSlope H r| ≤
      halfLineGreenAbsoluteFirstMoment H := by
  refine ⟨halfLineMinGreen_abs_le_firstMoment H hH hM hr, ?_⟩
  rw [halfLineMinGreen_sub_radius_slope_eq_firstMoment H hH r]
  change |∫ rho, (Iic r).indicator (fun t : ℝ => t * H t) rho
    ∂halfLineMeasure| ≤ ∫ rho, ‖rho * H rho‖ ∂halfLineMeasure
  calc
    _ ≤ ∫ rho, ‖(Iic r).indicator (fun t : ℝ => t * H t) rho‖
        ∂halfLineMeasure := abs_integral_le_integral_abs
    _ ≤ _ := by
      apply integral_mono_ae (hM.indicator measurableSet_Iic).norm hM.norm
      filter_upwards with rho
      by_cases hmem : rho ∈ Iic r
      · rw [indicator_of_mem hmem]
      · rw [indicator_of_notMem hmem, norm_zero]
        exact norm_nonneg _

/-- Exact physical trace after restoring an arbitrary FORCED affine
charge. Beyond the fixed affine cutoff the charge contributes to the
value, but cancels from the derivative of q/r. -/
theorem halfLineMinGreen_affine_physical_trace_firstMoment
    (H : ℝ → ℝ) (hH : Integrable H halfLineMeasure)
    (hM : Integrable (fun rho : ℝ => rho * H rho) halfLineMeasure)
    (a r : ℝ) (hr : 2 < r) :
    |affineRestore (halfLineMinGreen H) a r / r - a| ≤
      halfLineGreenAbsoluteFirstMoment H / r ∧
    |deriv (fun t : ℝ => affineRestore (halfLineMinGreen H) a t / t) r| ≤
      halfLineGreenAbsoluteFirstMoment H / r ^ 2 := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have hBounds := halfLineMinGreen_firstMoment_bounds H hH hM r hr0.le
  have hD := (halfLineMinGreen_C1_of_integrable H hH).1 r
  have hQuot : HasDerivAt (fun t : ℝ => halfLineMinGreen H t / t)
      ((halfLineL1GreenSlope H r * r - halfLineMinGreen H r) / r ^ 2) r := by
    simpa only [mul_one] using! hD.div (hasDerivAt_id r) hr0.ne'
  have hLocal :
      (fun t : ℝ => affineRestore (halfLineMinGreen H) a t / t) =ᶠ[𝓝 r]
        (fun t : ℝ => halfLineMinGreen H t / t + a) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    simp only [affineRestore, model_eq_id_of_two_le t ht.le,
      add_div, mul_div_cancel_right₀ a ht0.ne']
  have hRest := (hQuot.add_const a).congr_of_eventuallyEq hLocal
  have hValue : affineRestore (halfLineMinGreen H) a r / r - a =
      halfLineMinGreen H r / r := by
    simp only [affineRestore, model_eq_id_of_two_le r hr.le,
      add_div, mul_div_cancel_right₀ a hr0.ne', add_sub_cancel_right]
  constructor
  · rw [hValue, abs_div, abs_of_pos hr0]
    exact div_le_div_of_nonneg_right hBounds.1 hr0.le
  · rw [hRest.deriv, abs_div, abs_of_nonneg (sq_nonneg r)]
    have hNumerator :
        |halfLineL1GreenSlope H r * r - halfLineMinGreen H r| =
          |halfLineMinGreen H r - r * halfLineL1GreenSlope H r| := by
      rw [mul_comm, abs_sub_comm]
    rw [hNumerator]
    exact div_le_div_of_nonneg_right hBounds.2 (sq_nonneg r)

end HBL.Modulation.Monopole
