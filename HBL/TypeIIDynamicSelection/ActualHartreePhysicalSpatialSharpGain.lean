import HBL.TypeIIDynamicSelection.ActualHartreePhysicalSpatialCutoffSourceGain
import Mathlib.Tactic

/-!
# Original HBL 2.12: exact half-power in the localized radial PDE source

The actual critical radiation is f_ell = sqrt(ell) z(ell*r).
Keeping, rather than discarding, the sqrt(ell) in the physical
C1 field and derivative estimates gives O(ell^2 * sqrt(ell))
on the actual transition shell R <= r.

The result is SOURCE LEVEL: it neither assumes a blowup-rate law nor
asserts weighted Fredholm integrability, which must use shell
localization and a UNIFORM positive lower physical moment bound.
Original 2.12 remains open until the weighted regional source
and the full nonlocal mixed Hartree terms are controlled.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

private theorem radial_complex_commutator_norm_bound_sharp
    (u v w f g : ℂ) (C1 C2 A B ell : ℝ)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hell : 0 ≤ ell)
    (hu : ‖u‖ ≤ C1 * A * ell)
    (hv : ‖v‖ ≤ C2 * A ^ 2 * ell ^ 2)
    (hw : ‖w‖ ≤ 2 * A * ell)
    (hf : ‖f‖ ≤ Real.sqrt ell * B)
    (hg : ‖g‖ ≤ Real.sqrt ell * B * ell) :
    ‖(2 : ℂ) * u * g + (v + w * u) * f‖ ≤
      (2 * C1 * A * B + (C2 + 2 * C1) * A ^ 2 * B) * ell ^ 2 * Real.sqrt ell := by
  have hw_mul : ‖w * u‖ ≤
      (2 * A * ell) * (C1 * A * ell) := by
    rw [norm_mul]
    exact mul_le_mul hw hu (norm_nonneg _) (by positivity)
  have hcoeff : ‖v + w * u‖ ≤
      C2 * A ^ 2 * ell ^ 2 +
        (2 * A * ell) * (C1 * A * ell) := by
    calc
      ‖v + w * u‖ ≤ ‖v‖ + ‖w * u‖ := norm_add_le _ _
      _ ≤ C2 * A ^ 2 * ell ^ 2 +
          (2 * A * ell) * (C1 * A * ell) :=
        add_le_add hv hw_mul
  have hfirst : ‖u‖ * ‖g‖ ≤
      (C1 * A * ell) * (Real.sqrt ell * B * ell) :=
    mul_le_mul hu hg (norm_nonneg _) (by positivity)
  have hsecond : ‖v + w * u‖ * ‖f‖ ≤
      (C2 * A ^ 2 * ell ^ 2 +
        (2 * A * ell) * (C1 * A * ell)) * (Real.sqrt ell * B) :=
    mul_le_mul hcoeff hf (norm_nonneg _) (by positivity)
  calc
    ‖(2 : ℂ) * u * g + (v + w * u) * f‖ ≤
        ‖(2 : ℂ) * u * g‖ + ‖(v + w * u) * f‖ :=
          norm_add_le _ _
    _ = 2 * (‖u‖ * ‖g‖) + ‖v + w * u‖ * ‖f‖ := by
      have hnormTwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      simp only [norm_mul, hnormTwo]
      ring
    _ ≤ 2 * ((C1 * A * ell) * (Real.sqrt ell * B * ell)) +
        (C2 * A ^ 2 * ell ^ 2 +
          (2 * A * ell) * (C1 * A * ell)) * (Real.sqrt ell * B) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hfirst (by norm_num)) hsecond
    _ = (2 * C1 * A * B + (C2 + 2 * C1) * A ^ 2 * B) *
          ell ^ 2 * Real.sqrt ell := by ring

/-! Sharpened real Hartree radial spatial commutator. -/
theorem actual_Hartree_full_spatial_cutoff_source_sharp_length_gain
    (ell m M B r : ℝ)
    (hell : 0 < ell)
    (hm : 0 < m) (hmBound : m ≤ M)
    (hB : 0 ≤ B)
    (z : ℝ → ℂ)
    (hzSpace : ∀ x : ℝ, DifferentiableAt ℝ z (ell * x))
    (hzSecond : DifferentiableAt ℝ (deriv z) (ell * r))
    (hzBound : ‖z (ell * r)‖ ≤ B)
    (hzDerivBound : ‖deriv z (ell * r)‖ ≤ B)
    (hShell : actualHartreeMomentCutoffRadius ell m ≤ r) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ‖complexRadialLaplacian
          (fun x =>
            actualOneLayerInnerOverlapCutoff
                (actualHartreeMomentCutoffRadius ell m) x *
              rescalePhysicalRadiation ell z x) r -
        actualOneLayerInnerOverlapCutoff
            (actualHartreeMomentCutoffRadius ell m) r *
          complexRadialLaplacian (rescalePhysicalRadiation ell z) r‖ ≤
        (2 * C1 * (hartreeKappa * M / 4) * B +
          (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) *
          ell ^ 2 * Real.sqrt ell := by
  obtain ⟨C1,C2,hC1,hC2,hCut⟩ :=
    actual_Hartree_overlap_cutoff_uniform_C2_spatial_scaling
  let R : ℝ := actualHartreeMomentCutoffRadius ell m
  let A : ℝ := hartreeKappa * M / 4
  let f : ℝ → ℂ := rescalePhysicalRadiation ell z
  let χ : ℝ → ℂ := actualOneLayerInnerOverlapCutoff R
  have hM : 0 < M := lt_of_lt_of_le hm hmBound
  have hA : 0 ≤ A := by dsimp [A]; unfold hartreeKappa; positivity
  obtain ⟨hR,hRinv⟩ :=
    actual_Hartree_real_moment_radius_inverse_le ell m M hell hm hmBound
  have hr : 0 < r := hR.trans_le hShell
  have hFSize : ‖f r‖ ≤ Real.sqrt ell * B := by
    dsimp [f, rescalePhysicalRadiation]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg ell)]
    exact mul_le_mul_of_nonneg_left hzBound (Real.sqrt_nonneg ell)
  have hFder : ‖deriv f r‖ ≤ Real.sqrt ell * B * ell := by
    have hEq :
        ‖deriv (rescalePhysicalRadiation ell z) r‖ =
          Real.sqrt ell * ell * ‖deriv z (ell * r)‖ := by
      rw [actual_Hartree_critical_rescaled_radial_deriv ell r z (hzSpace r)]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg ell), abs_of_pos hell]
      ring
    change ‖deriv (rescalePhysicalRadiation ell z) r‖ ≤ _
    rw [hEq]
    calc
      Real.sqrt ell * ell * ‖deriv z (ell * r)‖ ≤
          Real.sqrt ell * ell * B :=
        mul_le_mul_of_nonneg_left hzDerivBound (by positivity)
      _ = Real.sqrt ell * B * ell := by ring
  have hχ1 : ‖deriv χ r‖ ≤ C1 * A * ell := by
    calc
      ‖deriv χ r‖ ≤ C1 / R := (hCut R r hR).1
      _ = C1 * (1 / R) := by field_simp [hR.ne']
      _ ≤ C1 * (A * ell) :=
        mul_le_mul_of_nonneg_left hRinv hC1.le
      _ = C1 * A * ell := by ring
  have hRInv2 : (1 / R) ^ 2 ≤ (A * ell) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hRinv 2
  have hχ2 : ‖deriv (deriv χ) r‖ ≤
      C2 * A ^ 2 * ell ^ 2 := by
    calc
      ‖deriv (deriv χ) r‖ ≤ C2 / R ^ 2 := (hCut R r hR).2
      _ = C2 * (1 / R) ^ 2 := by field_simp [hR.ne']
      _ ≤ C2 * (A * ell) ^ 2 :=
        mul_le_mul_of_nonneg_left hRInv2 hC2.le
      _ = C2 * A ^ 2 * ell ^ 2 := by ring
  have hrCoef : ‖(2 : ℂ) / (r : ℂ)‖ ≤ 2 * A * ell := by
    have hEq : ‖(2 : ℂ) / (r : ℂ)‖ = (2 : ℝ) / r := by
      have hnormTwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      simp only [norm_div, hnormTwo, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
    calc
      ‖(2 : ℂ) / (r : ℂ)‖ = (2 : ℝ) / r := hEq
      _ ≤ 2 / R :=
        actual_Hartree_radial_shell_two_over_r_le_two_over_R hR hShell
      _ = 2 * (1 / R) := by field_simp [hR.ne']
      _ ≤ 2 * (A * ell) :=
        mul_le_mul_of_nonneg_left hRinv (by norm_num)
      _ = 2 * A * ell := by ring
  have hχSpace : ∀ x : ℝ, DifferentiableAt ℝ χ x :=
    fun x => (actual_one_layer_overlap_cutoff_hasDerivAt R x).differentiableAt
  have hχSecond : DifferentiableAt ℝ (deriv χ) r :=
    (actual_one_layer_overlap_cutoff_deriv_hasDerivAt
      R r hR.ne').differentiableAt
  have hFSpace : ∀ x : ℝ, DifferentiableAt ℝ f x := by
    intro x
    have hscale : HasDerivAt (fun y : ℝ => ell * y) ell x :=
      hasDerivAt_const_mul ell
    have h := ((hzSpace x).hasDerivAt.scomp x hscale).const_mul
      (Real.sqrt ell : ℂ)
    exact h.differentiableAt
  have hFfirstEq :
      deriv f =
        fun x => (Real.sqrt ell : ℂ) *
          ((ell : ℂ) * deriv z (ell * x)) := by
    funext x
    exact actual_Hartree_critical_rescaled_radial_deriv
      ell x z (hzSpace x)
  have hFSecond : DifferentiableAt ℝ (deriv f) r := by
    rw [hFfirstEq]
    have hscale : HasDerivAt (fun y : ℝ => ell * y) ell r :=
      hasDerivAt_const_mul ell
    have h := ((hzSecond.hasDerivAt.scomp r hscale).const_mul
      (ell : ℂ)).const_mul (Real.sqrt ell : ℂ)
    exact h.differentiableAt
  have hSource := actual_one_layer_radial_Laplacian_cutoff_commutator
    χ f r hχSpace hFSpace hχSecond hFSecond
  have hNorm :
      ‖complexRadialLaplacian (fun x => χ x * f x) r -
          χ r * complexRadialLaplacian f r‖ ≤
        (2 * C1 * A * B + (C2 + 2 * C1) * A ^ 2 * B) *
          ell ^ 2 * Real.sqrt ell := by
    rw [hSource]
    exact radial_complex_commutator_norm_bound_sharp
      (deriv χ r) (deriv (deriv χ) r) ((2 : ℂ) / (r : ℂ))
      (f r) (deriv f r)
      C1 C2 A B ell hC1.le hC2.le hA hB hell.le
      hχ1 hχ2 hrCoef hFSize hFder
  refine ⟨C1,C2,hC1,hC2,?_⟩
  simpa only [A] using hNorm

end HBL.TypeIIDynamicSelection
