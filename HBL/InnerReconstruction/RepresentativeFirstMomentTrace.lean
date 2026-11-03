import HBL.InnerReconstruction.GreenFirstMomentTrace
import HBL.InnerReconstruction.RepresentativeBound
import Mathlib.Tactic

/-!
The reconstructed source is a*g + F, not the external source F alone.
Its first moment is proved integrable from the actual L2 Hilbert datum
and weighted F. The trace bound uses the existing explicit innerGreenBound.
Uniform smallness of the normalized datum g remains a separate obligation.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

def innerGreenTotalSource (g : RealL2 halfLineMeasure) (F : ℝ → ℝ) : ℝ → ℝ :=
  fun r => weightedGreenDecay r * g r + F r

/-- Quantitative first-moment bridge for the ACTUAL reconstructed source. -/
theorem innerGreenRepresentative_total_source_firstMoment
    (g : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 3 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    Integrable (innerGreenTotalSource g F) halfLineMeasure ∧
    Integrable (fun rho => rho * innerGreenTotalSource g F rho) halfLineMeasure ∧
    innerGreenRepresentative g F = halfLineMinGreen (innerGreenTotalSource g F) ∧
    halfLineGreenAbsoluteFirstMoment (innerGreenTotalSource g F) ≤ innerGreenBound g F := by
  let A : ℝ → ℝ := fun rho => weightedGreenDecay rho * g rho
  have hA : Integrable A halfLineMeasure := weightedGreen_source_integrable g
  have hF0 := weightedSource_integrable sigma (by linarith) F hF
  have hF1 := weightedSource_firstMoment_integrable sigma hsigma F hF
  have hA1 : Integrable (fun rho : ℝ => rho * A rho) halfLineMeasure := by
    apply (weightedGreenOutputMajorant_mul_integrable g).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    have hr0 : 0 < rho := hrho
    dsimp [weightedGreenOutputMajorant, A]
    rw [abs_of_pos hr0]
    ring
  have hTot0 : Integrable (innerGreenTotalSource g F) halfLineMeasure := hA.add hF0
  have hTot1 : Integrable (fun rho => rho * innerGreenTotalSource g F rho)
      halfLineMeasure := by
    apply (hA1.add hF1).congr
    filter_upwards with rho
    change rho * A rho + rho * F rho = rho * (A rho + F rho)
    ring
  have hEq : innerGreenRepresentative g F =
      halfLineMinGreen (innerGreenTotalSource g F) := by
    funext r
    change (∫ rho, min r rho * A rho ∂halfLineMeasure) +
      (∫ rho, min r rho * F rho ∂halfLineMeasure) =
      ∫ rho, min r rho * (A rho + F rho) ∂halfLineMeasure
    rw [← integral_add (halfLineMinGreen_kernel_integrable A hA r)
      (halfLineMinGreen_kernel_integrable F hF0 r)]
    apply integral_congr_ae
    filter_upwards with rho
    ring
  refine ⟨hTot0, hTot1, hEq, ?_⟩
  change (∫ rho, ‖rho * (A rho + F rho)‖ ∂halfLineMeasure) ≤
    weightedGreenPrimitiveBound g + ∫ rho, ‖rho * F rho‖ ∂halfLineMeasure
  calc
    _ ≤ ∫ rho, (‖rho * A rho‖ + ‖rho * F rho‖) ∂halfLineMeasure := by
      apply integral_mono_ae hTot1.norm (hA1.norm.add hF1.norm)
      filter_upwards with rho
      change ‖rho * (A rho + F rho)‖ ≤ ‖rho * A rho‖ + ‖rho * F rho‖
      rw [mul_add]
      exact norm_add_le _ _
    _ = (∫ rho, ‖rho * A rho‖ ∂halfLineMeasure) +
        (∫ rho, ‖rho * F rho‖ ∂halfLineMeasure) :=
      integral_add hA1.norm hF1.norm
    _ = weightedGreenPrimitiveBound g + ∫ rho, ‖rho * F rho‖ ∂halfLineMeasure := by
      congr 1
      unfold weightedGreenPrimitiveBound
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
      have hr0 : 0 < rho := hrho
      dsimp [weightedGreenOutputMajorant, A]
      rw [abs_of_pos hr0]
      congr 1
      ring

/-- A finite, explicit trace bound for each genuine normalized Green
reconstruction. It retains a and controls u-a and u', not just q and q'. -/
theorem innerGreenRepresentative_affine_physical_trace_bounds
    (g : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 3 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (a r : ℝ) (hr : 2 < r) :
    |affineRestore (innerGreenRepresentative g F) a r / r - a| ≤
      innerGreenBound g F / r ∧
    |deriv (fun t : ℝ => affineRestore (innerGreenRepresentative g F) a t / t) r| ≤
      innerGreenBound g F / r ^ 2 := by
  obtain ⟨h0, h1, hEq, hM⟩ :=
    innerGreenRepresentative_total_source_firstMoment g sigma hsigma F hF
  have hTrace := halfLineMinGreen_affine_physical_trace_firstMoment
    (innerGreenTotalSource g F) h0 h1 a r hr
  rw [hEq]
  have hr0 : 0 ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  exact ⟨hTrace.1.trans (div_le_div_of_nonneg_right hM hr0),
    hTrace.2.trans (div_le_div_of_nonneg_right hM (sq_nonneg r))⟩

end HBL.Modulation.Monopole
