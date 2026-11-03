import HBL.InnerReconstruction.GreenKernelIntegrable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
The min-kernel Green primitive of an L1 source is C1.  Continuity of the
source is unnecessary for the first derivative.  The corner rho=r is
null for the original half-line Lebesgue measure, and the difference
quotients are dominated by |F(rho)|.  This is the trace-regularity step,
not a classical second-derivative or nonlinear matching theorem.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The actual outgoing slope, with the original half-line measure. -/
def halfLineL1GreenSlope (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ rho, (Ioi r).indicator F rho ∂halfLineMeasure

/-- Canonical C1 Green reconstruction for merely integrable forcing.
No continuity of F and no representative of an L2 equivalence class
is differentiated.  Both the derivative and its continuity are proved. -/
theorem halfLineMinGreen_C1_of_integrable
    (F : ℝ → ℝ) (hF : Integrable F halfLineMeasure) :
    (∀ r : ℝ, HasDerivAt (halfLineMinGreen F)
      (halfLineL1GreenSlope F r) r) ∧
    Continuous (halfLineL1GreenSlope F) := by
  have hNe (r : ℝ) : ∀ᵐ rho : ℝ ∂halfLineMeasure, rho ≠ r := by
    apply ae_iff.mpr
    simp
  have hMeas (x : ℝ) :
      AEStronglyMeasurable ((Ioi x).indicator F) halfLineMeasure :=
    hF.aestronglyMeasurable.indicator measurableSet_Ioi
  have hLip (rho : ℝ) :
      LipschitzWith (Real.nnabs ‖F rho‖)
        (fun x : ℝ => min x rho * F rho) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← sub_mul, abs_mul, Real.dist_eq]
    change |min x rho - min y rho| * |F rho| ≤
      |‖F rho‖| * |x - y|
    calc
      _ ≤ |x - y| * |F rho| :=
        mul_le_mul_of_nonneg_right
          (abs_min_sub_min_le_max x rho y rho |>.trans_eq (by simp))
          (abs_nonneg _)
      _ = _ := by rw [Real.norm_eq_abs, abs_abs]; ring
  have hDer (r : ℝ) :
      HasDerivAt (halfLineMinGreen F) (halfLineL1GreenSlope F r) r := by
    have hDiff : ∀ᵐ rho : ℝ ∂halfLineMeasure,
        HasDerivAt (fun x : ℝ => min x rho * F rho)
          ((Ioi r).indicator F rho) r := by
      filter_upwards [hNe r] with rho hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have heq : (fun x : ℝ => min x rho * F rho) =ᶠ[𝓝 r]
            (fun _ : ℝ => rho * F rho) := by
          filter_upwards [Ioi_mem_nhds hlt] with x hx
          rw [min_eq_right hx.le]
        rw [indicator_of_notMem (show rho ∉ Ioi r from not_lt.mpr hlt.le)]
        exact (hasDerivAt_const r (rho * F rho)).congr_of_eventuallyEq heq
      · have heq : (fun x : ℝ => min x rho * F rho) =ᶠ[𝓝 r]
            (fun x : ℝ => x * F rho) := by
          filter_upwards [Iio_mem_nhds hgt] with x hx
          rw [min_eq_left hx.le]
        rw [indicator_of_mem (show rho ∈ Ioi r from hgt)]
        have hid : HasDerivAt (fun x : ℝ => x * F rho) (F rho) r := by
          simpa using! (hasDerivAt_id r).mul_const (F rho)
        exact hid.congr_of_eventuallyEq heq
    have h := hasDerivAt_integral_of_dominated_loc_of_lip
      (F := fun x rho : ℝ => min x rho * F rho)
      (F' := (Ioi r).indicator F) (bound := fun rho => ‖F rho‖)
      (s := Set.univ) (μ := halfLineMeasure)
      (Filter.univ_mem : (Set.univ : Set ℝ) ∈ 𝓝 r)
      (Filter.Eventually.of_forall fun x =>
        (halfLineMinGreen_kernel_integrable F hF x).aestronglyMeasurable)
      (halfLineMinGreen_kernel_integrable F hF r)
      (hMeas r)
      (Filter.Eventually.of_forall fun rho => (hLip rho).lipschitzOnWith)
      hF.norm hDiff
    exact h.2
  refine ⟨hDer, ?_⟩
  apply continuous_iff_continuousAt.mpr
  intro r
  have hBound : ∀ x : ℝ, ∀ᵐ rho : ℝ ∂halfLineMeasure,
      ‖(Ioi x).indicator F rho‖ ≤ ‖F rho‖ := by
    intro x
    filter_upwards with rho
    by_cases hmem : rho ∈ Ioi x
    · rw [indicator_of_mem hmem]
    · rw [indicator_of_notMem hmem, norm_zero]
      exact norm_nonneg _
  have hLim : ∀ᵐ rho : ℝ ∂halfLineMeasure,
      Tendsto (fun x : ℝ => (Ioi x).indicator F rho)
        (𝓝 r) (𝓝 ((Ioi r).indicator F rho)) := by
    filter_upwards [hNe r] with rho hne
    have heq : (fun x : ℝ => (Ioi x).indicator F rho) =ᶠ[𝓝 r]
        (fun _ : ℝ => (Ioi r).indicator F rho) := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · filter_upwards [Ioi_mem_nhds hlt] with x hx
        rw [indicator_of_notMem (show rho ∉ Ioi x from not_lt.mpr hx.le),
          indicator_of_notMem (show rho ∉ Ioi r from not_lt.mpr hlt.le)]
      · filter_upwards [Iio_mem_nhds hgt] with x hx
        rw [indicator_of_mem (show rho ∈ Ioi x from hx),
          indicator_of_mem (show rho ∈ Ioi r from hgt)]
    exact tendsto_const_nhds.congr' heq.symm
  exact tendsto_integral_filter_of_dominated_convergence
    (fun rho => ‖F rho‖) (Filter.Eventually.of_forall hMeas)
    (Filter.Eventually.of_forall hBound) hF.norm hLim

end HBL.Modulation.Monopole
