import HBL.TypeIIDynamicSelection.ActualOneLayerMovingParametrixTransport
import Mathlib.Tactic

/-!
# HBL original 2.12: genuine radial overlap cutoff second derivative bounds

The ORIGINAL smooth Hartree cutoff chi_R(r)=1-cutoff(r/R)
has exactly the physical spatial factors R^(-1) and R^(-2).
The fixed second-derivative constant is DERIVED from the smooth
cutoff on its compact [1,2] transition, plus its two constant
extensions. No source order or new axiom is introduced.

These are the real coefficients in the previously strict accepted
full radial Laplacian commutator. Full original 2.12 still needs
physical region correction estimates and all generated remainder
source gains.
-/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_fixed_Hartree_overlap_cutoff_second_deriv_zero_left
    {x : ℝ} (hx : x < 1) :
    deriv (deriv cutoff) x = 0 := by
  have he : deriv cutoff =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact cutoff_deriv_zero_of_lt_one hy
  rw [he.deriv_eq]
  exact deriv_const x 0

theorem actual_fixed_Hartree_overlap_cutoff_second_deriv_zero_right
    {x : ℝ} (hx : 2 < x) :
    deriv (deriv cutoff) x = 0 := by
  have he : deriv cutoff =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact actual_fixed_cutoff_deriv_zero_of_gt_two hy
  rw [he.deriv_eq]
  exact deriv_const x 0

/-- One globally valid second-cutoff-derivative constant derived
from the true original C-infinity radial cutoff. -/
theorem exists_actual_fixed_Hartree_cutoff_uniform_second_deriv_bound :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ x : ℝ, |deriv (deriv cutoff) x| ≤ C2 := by
  have hD1 : ContDiff ℝ ∞ (deriv cutoff) :=
    (contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).2
  have hD2 : Continuous (deriv (deriv cutoff)) :=
    ((contDiff_infty_iff_deriv.mp hD1).2).continuous
  obtain ⟨C,hC⟩ :=
    IsCompact.exists_bound_of_continuousOn
      (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)) hD2.continuousOn
  have hCnonneg : 0 ≤ C := by
    have hOne := hC 1 (show (1 : ℝ) ∈ Icc 1 2 by norm_num)
    exact (norm_nonneg (deriv (deriv cutoff) 1)).trans hOne
  refine ⟨C + 1, by linarith, ?_⟩
  intro x
  by_cases hleft : x < 1
  · rw [actual_fixed_Hartree_overlap_cutoff_second_deriv_zero_left hleft,
      abs_zero]
    linarith
  · by_cases hright : 2 < x
    · rw [actual_fixed_Hartree_overlap_cutoff_second_deriv_zero_right hright,
        abs_zero]
      linarith
    · have hx : x ∈ Icc (1 : ℝ) 2 :=
        ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
      have hb := hC x hx
      rw [Real.norm_eq_abs] at hb
      linarith

/-- Strict original Hartree radial overlap first and second derivative
costs follow from the physical cutoff, uniformly for ALL positive
moving radii R and all observation points r. -/
theorem actual_Hartree_overlap_cutoff_uniform_C2_spatial_scaling :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ R r : ℝ, 0 < R →
        ‖deriv (actualOneLayerInnerOverlapCutoff R) r‖ ≤ C1 / R ∧
        ‖deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r‖ ≤
          C2 / R ^ 2 := by
  obtain ⟨C1,hC1,hD1⟩ := exists_actual_fixed_cutoff_uniform_deriv_bound
  obtain ⟨C2,hC2,hD2⟩ :=
    exists_actual_fixed_Hartree_cutoff_uniform_second_deriv_bound
  refine ⟨C1,C2,hC1,hC2,?_⟩
  intro R r hR
  constructor
  · rw [(actual_one_layer_overlap_cutoff_hasDerivAt R r).deriv,
      Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_neg, abs_of_pos hR]
    exact div_le_div_of_nonneg_right (hD1 (r / R)) hR.le
  · rw [(actual_one_layer_overlap_cutoff_deriv_hasDerivAt
      R r hR.ne').deriv,
      Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_neg, abs_of_pos (pow_pos hR 2)]
    exact div_le_div_of_nonneg_right (hD2 (r / R)) (sq_nonneg R)

/-- The true radial 2/r coefficient adds no loss beyond 2/R on
the original physical transition annulus. -/
theorem actual_Hartree_radial_shell_two_over_r_le_two_over_R
    {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    (2 : ℝ) / r ≤ 2 / R := by
  have hrpos : 0 < r := hR.trans_le hr
  have hratio : (1 : ℝ) ≤ r / R := by
    apply (le_div_iff₀ hR).2
    simpa only [one_mul] using hr
  apply (div_le_iff₀ hrpos).2
  calc
    (2 : ℝ) = 2 * 1 := by ring
    _ ≤ 2 * (r / R) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = (2 / R) * r := by ring

end HBL.TypeIIDynamicSelection
