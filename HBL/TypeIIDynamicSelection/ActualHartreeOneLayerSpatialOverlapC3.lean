import HBL.TypeIIDynamicSelection.ActualOneLayerSpatialOverlapGain
import Mathlib.Tactic

/-!
# Original moving Hartree radial cutoff THIRD derivative

The Morawetz-dual norm of the genuine spatial Laplacian commutator
differentiates the original moving physical cutoff one more time.
Second-order cutoff estimates do NOT by themselves control that
derivative. Here the actual already-used C-infinity cutoff supplies a
true R^{-3} third derivative, uniformly at all positive radii.

This only closes the cutoff geometry producer. It assumes no physical
Hartree source derivative bound, time decay or blowup rate, and does
not close original 2.13.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

private theorem actual_fixed_Hartree_overlap_cutoff_third_deriv_zero_left
    {x : ℝ} (hx : x < 1) :
    deriv (deriv (deriv cutoff)) x = 0 := by
  have he : deriv (deriv cutoff) =ᶠ[𝓝 x]
      (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact actual_fixed_Hartree_overlap_cutoff_second_deriv_zero_left hy
  rw [he.deriv_eq]
  exact deriv_const x 0

private theorem actual_fixed_Hartree_overlap_cutoff_third_deriv_zero_right
    {x : ℝ} (hx : 2 < x) :
    deriv (deriv (deriv cutoff)) x = 0 := by
  have he : deriv (deriv cutoff) =ᶠ[𝓝 x]
      (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact actual_fixed_Hartree_overlap_cutoff_second_deriv_zero_right hy
  rw [he.deriv_eq]
  exact deriv_const x 0

/-- A genuine constant for the THIRD derivative of the true cutoff,
by compactness and the two constant exterior regions. -/
theorem exists_actual_fixed_Hartree_cutoff_uniform_third_deriv_bound :
    ∃ C3 : ℝ, 0 < C3 ∧
      ∀ x : ℝ, |deriv (deriv (deriv cutoff)) x| ≤ C3 := by
  have hD1 : ContDiff ℝ ∞ (deriv cutoff) :=
    (contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).2
  have hD2 : ContDiff ℝ ∞ (deriv (deriv cutoff)) :=
    (contDiff_infty_iff_deriv.mp hD1).2
  have hD3 : Continuous (deriv (deriv (deriv cutoff))) :=
    ((contDiff_infty_iff_deriv.mp hD2).2).continuous
  obtain ⟨C, hC⟩ :=
    IsCompact.exists_bound_of_continuousOn
      (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)) hD3.continuousOn
  have hCnonneg : 0 ≤ C := by
    have hOne := hC 1 (show (1 : ℝ) ∈ Icc 1 2 by norm_num)
    exact (norm_nonneg (deriv (deriv (deriv cutoff)) 1)).trans hOne
  refine ⟨C + 1, by linarith, ?_⟩
  intro x
  by_cases hleft : x < 1
  · rw [actual_fixed_Hartree_overlap_cutoff_third_deriv_zero_left hleft, abs_zero]
    linarith
  · by_cases hright : 2 < x
    · rw [actual_fixed_Hartree_overlap_cutoff_third_deriv_zero_right hright, abs_zero]
      linarith
    · have hx : x ∈ Icc (1 : ℝ) 2 :=
        ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
      have hb := hC x hx
      rw [Real.norm_eq_abs] at hb
      linarith

/-- Exact spatial C³ chain rule for the *original* overlap cutoff.
The derivative is not replaced by a bounded symbolic source. -/
theorem actual_Hartree_real_overlap_cutoff_third_hasDerivAt
    (R r : ℝ) (hR : R ≠ 0) :
    HasDerivAt (deriv (deriv (actualOneLayerInnerOverlapCutoff R)))
      ((-deriv (deriv (deriv cutoff)) (r / R) / R ^ 3 : ℝ) : ℂ) r := by
  have hsecond : deriv (deriv (actualOneLayerInnerOverlapCutoff R)) =
      fun x => ((-deriv (deriv cutoff) (x / R) / R ^ 2 : ℝ) : ℂ) :=
    funext (fun x =>
      (actual_one_layer_overlap_cutoff_deriv_hasDerivAt R x hR).deriv)
  rw [hsecond]
  have hscale : HasDerivAt (fun x : ℝ => x / R) (1 / R) r :=
    (hasDerivAt_id r).div_const R
  have hcut1 : ContDiff ℝ ∞ (deriv cutoff) :=
    (contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).2
  have hcut2 : ContDiff ℝ ∞ (deriv (deriv cutoff)) :=
    (contDiff_infty_iff_deriv.mp hcut1).2
  have hcut : HasDerivAt (deriv (deriv cutoff))
      (deriv (deriv (deriv cutoff)) (r / R)) (r / R) :=
    (hcut2.differentiable (by norm_num) (r / R)).hasDerivAt
  have hreal : HasDerivAt
      (fun x : ℝ => -deriv (deriv cutoff) (x / R) / R ^ 2)
      (-deriv (deriv (deriv cutoff)) (r / R) / R ^ 3) r := by
    convert ((hcut.comp r hscale).div_const (R ^ 2)).neg using 1
    · funext x
      simp only [Pi.neg_apply, Function.comp_def]
      ring
    · field_simp [hR]
      ring
  exact hreal.ofReal_comp

/-- The third physical derivative costs exactly R^{-3},
with a constant coming from the original smooth cutoff. -/
theorem actual_Hartree_overlap_cutoff_uniform_C3_spatial_scaling :
    ∃ C3 : ℝ, 0 < C3 ∧
      ∀ R r : ℝ, 0 < R →
        ‖deriv (deriv (deriv (actualOneLayerInnerOverlapCutoff R))) r‖ ≤
          C3 / R ^ 3 := by
  obtain ⟨C3, hC3, hBound⟩ :=
    exists_actual_fixed_Hartree_cutoff_uniform_third_deriv_bound
  refine ⟨C3, hC3, ?_⟩
  intro R r hR
  rw [(actual_Hartree_real_overlap_cutoff_third_hasDerivAt R r hR.ne').deriv,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (pow_pos hR 3)]
  exact div_le_div_of_nonneg_right (hBound (r / R)) (pow_nonneg hR.le 3)

end HBL.TypeIIDynamicSelection
