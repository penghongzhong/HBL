import HBL.TypeIIDynamicSelection.ActualOneLayerMovingParametrixTransport
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalSpatialSharpGain
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalNonlocalSharpGain
import Mathlib.Tactic

/-!
# HBL original 2.12: a single true full radial Hartree moving-cutoff residual

This combines the entire exact original radial renormalized Hartree PDE
cutoff residual, including the true moving material transport, the
radial Laplacian second derivative, and the COMPLETE inverse-square
quartic nonlocal Hartree operator.

No abstract GeneratedTerm, no fabricated regional source, and no
prescribed Type-II exponent appears. The actual physical radiation
f_ell=sqrt(ell)*z(ell*r) and the genuine physical moment cutoff
R=4/(kappa_H*ell*m) remain explicit.

On the true overlap shell R<=r<=2R, the two sharp elliptic/nonlocal
commutators retain O(ell^(5/2)); the remaining transport factor is
the exactly identified physical relative radius drift R_s/R-b.
The latter must be discharged by the actual Hartree moment PDE
before this is a strictly positive whole-source bound.

Still open: the Kummer/remote/Frobenius and all-weight source norms
and the full original minimal weight cluster theorem.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- This is the norm inequality for ONE genuine residual identity.
Every term on the right is the actual physical PDE operator. -/
theorem actual_Hartree_full_moving_cutoff_residual_triangle
    (R : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (b omega : ℝ) {s r Rs : ℝ}
    (hR : HasDerivAt R Rs s) (hRne : R s ≠ 0)
    (hfTime : DifferentiableAt ℝ (fun t => f t r) s)
    (hfSpace : ∀ x : ℝ, DifferentiableAt ℝ (f s) x)
    (hf2 : DifferentiableAt ℝ (deriv (f s)) r) :
    ‖complexRadialRenormalizedResidual
        (fun t x => actualOneLayerInnerOverlapCutoff (R t) x * f t x)
        b omega s r -
      actualOneLayerInnerOverlapCutoff (R s) r *
        complexRadialRenormalizedResidual f b omega s r‖ ≤
      ‖Complex.I *
        (actualOneLayerMaterialCutoffCoefficient (R s) Rs b r : ℂ) *
          f s r‖ +
      ‖complexRadialLaplacian
        (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialLaplacian (f s) r‖ +
      ‖complexRadialHartreeNonlinearity
        (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialHartreeNonlinearity (f s) r‖ := by
  have hFull := actual_one_layer_moving_parametrix_true_Hartree_source
    R f b omega hR hRne hfTime hfSpace hf2 (r := r)
  have hLap := actual_one_layer_physical_cutoff_radial_commutator
    (R s) r hRne (f s) hfSpace hf2
  have hEq :
      complexRadialRenormalizedResidual
        (fun t x => actualOneLayerInnerOverlapCutoff (R t) x * f t x)
        b omega s r -
      actualOneLayerInnerOverlapCutoff (R s) r *
        complexRadialRenormalizedResidual f b omega s r =
      Complex.I *
        (actualOneLayerMaterialCutoffCoefficient (R s) Rs b r : ℂ) *
          f s r +
      (complexRadialLaplacian
        (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialLaplacian (f s) r) +
      (complexRadialHartreeNonlinearity
        (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialHartreeNonlinearity (f s) r) := by
    rw [hFull, hLap]
    ring
  rw [hEq]
  exact (norm_add_le _ _).trans
    (add_le_add_right (norm_add_le _ _) _)

/-- The full SAME-PDE profile-cutoff residual on the genuine
Hartree moment-moving shell. All local/nonlocal interactions are
now bounded together, and only the PHYSICAL drift R_s/R-b remains
instead of an abstract assigned weight. -/
theorem actual_Hartree_full_physical_cutoff_PDE_shell_sharp
    (R : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (b omega : ℝ) (s r Rs ell m M B D : ℝ)
    (hR : HasDerivAt R Rs s)
    (hRadius : R s = actualHartreeMomentCutoffRadius ell m)
    (hfTime : DifferentiableAt ℝ (fun t => f t r) s)
    (hfSpace : ∀ x : ℝ, DifferentiableAt ℝ (f s) x)
    (hf2 : DifferentiableAt ℝ (deriv (f s)) r)
    (hell : 0 < ell) (hm : 0 < m) (hmBound : m ≤ M)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hfProfile : f s = rescalePhysicalRadiation ell z)
    (hzSpace : ∀ x : ℝ, DifferentiableAt ℝ z (ell * x))
    (hzSecond : DifferentiableAt ℝ (deriv z) (ell * r))
    (hzAmp : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hzDerivBound : ‖deriv z (ell * r)‖ ≤ B)
    (hzQuartic : ∀ u : ℝ, 0 < u →
      ‖z u‖ ^ 4 ≤ D * bubble u ^ 2)
    (hShell : actualHartreeMomentCutoffRadius ell m ≤ r)
    (hShellRight : r ≤ 2 * actualHartreeMomentCutoffRadius ell m) :
    ∃ Cchi C1 C2 : ℝ,
      0 < Cchi ∧ 0 < C1 ∧ 0 < C2 ∧
      ‖complexRadialRenormalizedResidual
          (fun t x => actualOneLayerInnerOverlapCutoff (R t) x * f t x)
          b omega s r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialRenormalizedResidual f b omega s r‖ ≤
      (2 * Cchi * |Rs / R s - b|) * (Real.sqrt ell * B) +
      ((2 * C1 * (hartreeKappa * M / 4) * B +
        (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
        2 * radialHartreeRowBoundConstant * D * B ^ 3) *
          ell ^ 2 * Real.sqrt ell := by
  have hRpos : 0 < R s := by
    rw [hRadius]
    exact (actual_Hartree_real_moment_radius_inverse_le
      ell m M hell hm hmBound).1
  have hRne : R s ≠ 0 := hRpos.ne'
  have hRleft : R s ≤ r := by simpa only [hRadius] using hShell
  have hRright : r ≤ 2 * R s := by simpa only [hRadius] using hShellRight
  have hr : 0 < r := hRpos.trans_le hRleft
  obtain ⟨Cchi,hCchi,hMat⟩ :=
    actual_one_layer_material_transport_shell_bound
      (R s) Rs b r hRpos hRleft hRright
  obtain ⟨C1,C2,hC1,hC2,hLoc⟩ :=
    actual_Hartree_full_spatial_cutoff_source_sharp_length_gain
      ell m M B r hell hm hmBound hB z hzSpace hzSecond
      (hzAmp (ell * r) (mul_pos hell hr))
      hzDerivBound hShell
  have hNonlocal :=
    actual_Hartree_physical_nonlocal_cutoff_sharp_length_gain
      ell (R s) r B D hell hRpos hr hD hB z hz hzAmp hzQuartic
  have hField : ‖f s r‖ ≤ Real.sqrt ell * B := by
    rw [hfProfile]
    unfold rescalePhysicalRadiation
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg ell)]
    exact mul_le_mul_of_nonneg_left
      (hzAmp (ell * r) (mul_pos hell hr)) (Real.sqrt_nonneg ell)
  have hTimeTerm :
      ‖Complex.I *
        (actualOneLayerMaterialCutoffCoefficient (R s) Rs b r : ℂ) *
          f s r‖ ≤
      (2 * Cchi * |Rs / R s - b|) * (Real.sqrt ell * B) := by
    have hEq :
        ‖Complex.I *
          (actualOneLayerMaterialCutoffCoefficient (R s) Rs b r : ℂ) *
            f s r‖ =
        |actualOneLayerMaterialCutoffCoefficient (R s) Rs b r| *
          ‖f s r‖ := by
      simp only [norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hEq]
    exact mul_le_mul hMat hField (norm_nonneg _) (by positivity)
  have hLocal :
      ‖complexRadialLaplacian
        (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialLaplacian (f s) r‖ ≤
      (2 * C1 * (hartreeKappa * M / 4) * B +
        (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) *
          ell ^ 2 * Real.sqrt ell := by
    rw [hRadius, hfProfile]
    exact hLoc
  have hRiesz :
      ‖complexRadialHartreeNonlinearity
        (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialHartreeNonlinearity (f s) r‖ ≤
      (2 * radialHartreeRowBoundConstant * D * B ^ 3) *
          ell ^ 2 * Real.sqrt ell := by
    rw [hfProfile]
    exact hNonlocal
  have hSource := actual_Hartree_full_moving_cutoff_residual_triangle
    R f b omega hR hRne hfTime hfSpace hf2 (r := r)
  refine ⟨Cchi,C1,C2,hCchi,hC1,hC2,?_⟩
  calc
    _ ≤ ‖Complex.I *
        (actualOneLayerMaterialCutoffCoefficient (R s) Rs b r : ℂ) *
          f s r‖ +
      ‖complexRadialLaplacian
        (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialLaplacian (f s) r‖ +
      ‖complexRadialHartreeNonlinearity
        (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialHartreeNonlinearity (f s) r‖ := hSource
    _ ≤ (2 * Cchi * |Rs / R s - b|) * (Real.sqrt ell * B) +
        ((2 * C1 * (hartreeKappa * M / 4) * B +
          (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) *
          ell ^ 2 * Real.sqrt ell) +
        ((2 * radialHartreeRowBoundConstant * D * B ^ 3) *
          ell ^ 2 * Real.sqrt ell) :=
      add_le_add (add_le_add hTimeTerm hLocal) hRiesz
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
