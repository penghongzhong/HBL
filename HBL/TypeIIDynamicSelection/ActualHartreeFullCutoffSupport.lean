import HBL.TypeIIDynamicSelection.ActualHartreePhysicalNonlocalSharpGain
import HBL.TypeIIDynamicSelection.ActualOneLayerPDEResidual
import Mathlib.Tactic

/-!
# Actual HBL 2.12 cutoff PDE commutators have TRUE compact radial support

The Hartree nonlocality does not imply that its localized commutator
has a noncompact observation tail: the physical Hartree nonlinearity is
the inverse-square Riesz potential multiplied by the LOCAL cubic
factor |u(r)|^2 u(r). Outside the actual overlap radius 2R,
the fixed original cutoff is zero, hence both nonlinear terms
vanish, regardless of the Riesz interaction at distant points.

The full radial Laplacian commutator also vanishes for r>2R,
because both true cutoff derivatives vanish there. These are
identities about the actual original operators and smooth cutoff,
not abstract hypotheses asserting a support bound.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual inner overlap cutoff is exactly zero outside 2R. -/
theorem actual_Hartree_inner_overlap_cutoff_far_zero
    (R r : ℝ) (hR : 0 < R) (hfar : 2 * R ≤ r) :
    actualOneLayerInnerOverlapCutoff R r = 0 := by
  have hr : (2 : ℝ) ≤ r / R :=
    (le_div_iff₀ hR).2 (by simpa only [mul_comm] using hfar)
  unfold actualOneLayerInnerOverlapCutoff
  rw [cutoff_one_of_two_le (r / R) hr]
  norm_num

/-- The FULL nonlocal quartic inverse-square Hartree commutator is
supported in the actual r<=2R inner/transition region, despite the
global spatial Riesz potential. -/
theorem actual_Hartree_nonlocal_cutoff_far_source_zero
    (R r : ℝ) (hR : 0 < R) (hfar : 2 * R ≤ r)
    (f : ℝ → ℂ) :
    complexRadialHartreeNonlinearity
        (fun x => actualOneLayerInnerOverlapCutoff R x * f x) r -
      actualOneLayerInnerOverlapCutoff R r *
        complexRadialHartreeNonlinearity f r = 0 := by
  have hz : actualOneLayerInnerOverlapCutoff R r = 0 :=
    actual_Hartree_inner_overlap_cutoff_far_zero R r hR hfar
  unfold complexRadialHartreeNonlinearity
  simp only [hz, zero_mul, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Complex.ofReal_zero, mul_zero, sub_zero]

/-- Both radial derivative costs R^(-1) and R^(-2) vanish
identically in the far field of the TRUE 3D radial Laplacian. -/
theorem actual_Hartree_radial_Laplacian_cutoff_far_source_zero
    (R r : ℝ) (hR : 0 < R) (hfar : 2 * R < r)
    (f : ℝ → ℂ)
    (hf : ∀ x : ℝ, DifferentiableAt ℝ f x)
    (hf2 : DifferentiableAt ℝ (deriv f) r) :
    complexRadialLaplacian
        (fun x => actualOneLayerInnerOverlapCutoff R x * f x) r -
      actualOneLayerInnerOverlapCutoff R r *
        complexRadialLaplacian f r = 0 := by
  have hr : (2 : ℝ) < r / R :=
    (lt_div_iff₀ hR).2 (by simpa only [mul_comm] using hfar)
  have hd1 : deriv cutoff (r / R) = 0 :=
    actual_fixed_cutoff_deriv_zero_of_gt_two hr
  have hd2 : deriv (deriv cutoff) (r / R) = 0 :=
    actual_fixed_Hartree_overlap_cutoff_second_deriv_zero_right hr
  rw [actual_one_layer_physical_cutoff_radial_commutator R r hR.ne' f hf hf2]
  simp only [hd1, hd2, neg_zero, zero_div, Complex.ofReal_zero,
    zero_mul, add_zero, zero_add]

end HBL.TypeIIDynamicSelection
