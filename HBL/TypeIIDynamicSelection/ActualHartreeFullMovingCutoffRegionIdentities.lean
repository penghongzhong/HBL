import HBL.TypeIIDynamicSelection.ActualHartreeFullMovingCutoffResidualSharp
import HBL.TypeIIDynamicSelection.ActualHartreeFullCutoffSupport
import Mathlib.Tactic

/-!
# Exact radial core/outside supports for the SAME true moving Hartree residual

The genuine 3D inverse-square quartic Hartree Riesz term is NOT local:
the nonlocal source can be nonzero even where the smooth overlap
chi_R is identically 1. The correct identity is:

  core 0<r<R:   [full physical PDE residual,chi_R] f
                  = N(chi_R f)-chi_R N(f)
  far  r>2R:   [full physical PDE residual,chi_R] f = 0.

On the core, both actual time/dilation material transport AND the
radial Laplacian commutator vanish; only the genuine remote Riesz
potential remains. On the outer region every term vanishes because
of the local |u|^2 u Hartree factor, even though the convolution
potential itself is global.

This is the physical structural equality needed to piece together
the full weighted three-region residual in the original manuscript
2.12; the Kummer/remote corrections themselves remain open.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_material_overlap_core_zero
    (R Rs b r : ℝ) (hR : 0 < R) (hr : r < R) :
    actualOneLayerMaterialCutoffCoefficient R Rs b r = 0 := by
  have harg : r / R < 1 := (div_lt_iff₀ hR).2 (by simpa using hr)
  have hd : deriv cutoff (r / R) = 0 :=
    cutoff_deriv_zero_of_lt_one harg
  simp [actualOneLayerMaterialCutoffCoefficient, hd]

theorem actual_Hartree_material_overlap_far_zero
    (R Rs b r : ℝ) (hR : 0 < R) (hr : 2 * R < r) :
    actualOneLayerMaterialCutoffCoefficient R Rs b r = 0 := by
  have harg : 2 < r / R := (lt_div_iff₀ hR).2 (by simpa using hr)
  have hd : deriv cutoff (r / R) = 0 :=
    actual_fixed_cutoff_deriv_zero_of_gt_two harg
  simp [actualOneLayerMaterialCutoffCoefficient, hd]

theorem actual_Hartree_radial_Laplacian_cutoff_core_source_zero
    (R r : ℝ) (hR : 0 < R) (hr : r < R)
    (f : ℝ → ℂ)
    (hf : ∀ x : ℝ, DifferentiableAt ℝ f x)
    (hf2 : DifferentiableAt ℝ (deriv f) r) :
    complexRadialLaplacian
        (fun x => actualOneLayerInnerOverlapCutoff R x * f x) r -
      actualOneLayerInnerOverlapCutoff R r *
        complexRadialLaplacian f r = 0 := by
  have harg : r / R < 1 := (div_lt_iff₀ hR).2 (by simpa using hr)
  have hd1 : deriv cutoff (r / R) = 0 :=
    cutoff_deriv_zero_of_lt_one harg
  have hd2 : deriv (deriv cutoff) (r / R) = 0 :=
    actual_fixed_Hartree_overlap_cutoff_second_deriv_zero_left harg
  rw [actual_one_layer_physical_cutoff_radial_commutator R r hR.ne' f hf hf2]
  simp [hd1, hd2]

/-- The nonlocal source is the ONLY surviving true Hartree
full-moving-cutoff PDE commutator in the original radial core. -/
theorem actual_Hartree_true_moving_cutoff_core_residual_eq_Riesz
    (R : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (b omega : ℝ) {s r Rs : ℝ}
    (hR : HasDerivAt R Rs s) (hRpos : 0 < R s)
    (hr : r < R s)
    (hfTime : DifferentiableAt ℝ (fun t => f t r) s)
    (hfSpace : ∀ x : ℝ, DifferentiableAt ℝ (f s) x)
    (hf2 : DifferentiableAt ℝ (deriv (f s)) r) :
    complexRadialRenormalizedResidual
        (fun t x => actualOneLayerInnerOverlapCutoff (R t) x * f t x)
        b omega s r -
      actualOneLayerInnerOverlapCutoff (R s) r *
        complexRadialRenormalizedResidual f b omega s r =
      complexRadialHartreeNonlinearity
        (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialHartreeNonlinearity (f s) r := by
  have hFull := actual_one_layer_moving_parametrix_true_Hartree_source
    R f b omega hR hRpos.ne' hfTime hfSpace hf2 (r := r)
  have hLap := actual_one_layer_physical_cutoff_radial_commutator
    (R s) r hRpos.ne' (f s) hfSpace hf2
  have hm : actualOneLayerMaterialCutoffCoefficient
      (R s) Rs b r = 0 :=
    actual_Hartree_material_overlap_core_zero
      (R s) Rs b r hRpos hr
  have hlap := actual_Hartree_radial_Laplacian_cutoff_core_source_zero
    (R s) r hRpos hr (f s) hfSpace hf2
  rw [hFull, hLap]
  rw [hm, hlap]
  ring

/-- The entire exact PDE commutator vanishes in the remote r>2R
outer region, without incorrectly asserting the Riesz potential
itself is zero. -/
theorem actual_Hartree_true_moving_cutoff_far_residual_zero
    (R : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (b omega : ℝ) {s r Rs : ℝ}
    (hR : HasDerivAt R Rs s) (hRpos : 0 < R s)
    (hr : 2 * R s < r)
    (hfTime : DifferentiableAt ℝ (fun t => f t r) s)
    (hfSpace : ∀ x : ℝ, DifferentiableAt ℝ (f s) x)
    (hf2 : DifferentiableAt ℝ (deriv (f s)) r) :
    complexRadialRenormalizedResidual
        (fun t x => actualOneLayerInnerOverlapCutoff (R t) x * f t x)
        b omega s r -
      actualOneLayerInnerOverlapCutoff (R s) r *
        complexRadialRenormalizedResidual f b omega s r = 0 := by
  have hFull := actual_one_layer_moving_parametrix_true_Hartree_source
    R f b omega hR hRpos.ne' hfTime hfSpace hf2 (r := r)
  have hLap := actual_one_layer_physical_cutoff_radial_commutator
    (R s) r hRpos.ne' (f s) hfSpace hf2
  have hm : actualOneLayerMaterialCutoffCoefficient
      (R s) Rs b r = 0 :=
    actual_Hartree_material_overlap_far_zero
      (R s) Rs b r hRpos hr
  have hlap := actual_Hartree_radial_Laplacian_cutoff_far_source_zero
    (R s) r hRpos hr (f s) hfSpace hf2
  have hnl := actual_Hartree_nonlocal_cutoff_far_source_zero
    (R s) r hRpos hr.le (f s)
  rw [hFull, hLap]
  rw [hm, hlap, hnl]
  ring

end HBL.TypeIIDynamicSelection
