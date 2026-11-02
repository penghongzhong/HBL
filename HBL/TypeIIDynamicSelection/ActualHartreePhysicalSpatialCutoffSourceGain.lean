import HBL.TypeIIDynamicSelection.ActualHartreeMomentSpatialStrictGain
import HBL.TypeIIDynamicSelection.ActualHartreeRadialDilationScaling
import Mathlib.Tactic

/-!
# Original HBL 2.12: one true critical-scaled Hartree radiation, full LOCAL
# Laplacian cutoff commutator has strictly positive physical time gain

The actual Hartree radiation is f_ell(r)=sqrt(ell)*z(ell*r).
The actual moving cutoff radius is R=4/(kappa_H*ell*m), where m
is the genuine positive quartic Hartree physical radiation moment.

On the true transition shell R <= r, the full radial Laplacian
cutoff source is

   2 chi_R'(r) f_ell'(r)
   + (chi_R''(r)+(2/r)chi_R'(r)) f_ell(r).

The two *actual* C-infinity cutoff derivatives, full radial (2/r),
critical spatial chain rule and physical moment-radius identity
imply O(ell²) on the true shell from a uniform physical C¹ bound.
For beta>1/2 and ell<=C*s^-beta this is the genuine strictly
integrable time order 1+(2beta-1), not a GeneratedTerm supplied order.

This closes the ENTIRE local spatial cutoff-commutator gain class,
conditional on the same selected physical strong radial Hartree
trajectory having a genuine C¹ bound on the sampled shell.
The time/material cutoff class is separately proved. The full
nonlocal Riesz commutator and Kummer/Frobenius/parameter sources
remain mathematical obligations of manuscript original 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

private theorem radial_complex_commutator_norm_bound
    (u v w f g : ℂ) (C1 C2 A B ell : ℝ)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hell : 0 ≤ ell)
    (hu : ‖u‖ ≤ C1 * A * ell)
    (hv : ‖v‖ ≤ C2 * A ^ 2 * ell ^ 2)
    (hw : ‖w‖ ≤ 2 * A * ell)
    (hf : ‖f‖ ≤ B) (hg : ‖g‖ ≤ B * ell) :
    ‖(2 : ℂ) * u * g + (v + w * u) * f‖ ≤
      (2 * C1 * A * B + (C2 + 2 * C1) * A ^ 2 * B) * ell ^ 2 := by
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
      (C1 * A * ell) * (B * ell) :=
    mul_le_mul hu hg (norm_nonneg _) (by positivity)
  have hsecond : ‖v + w * u‖ * ‖f‖ ≤
      (C2 * A ^ 2 * ell ^ 2 +
        (2 * A * ell) * (C1 * A * ell)) * B :=
    mul_le_mul hcoeff hf (norm_nonneg _) (by positivity)
  calc
    ‖(2 : ℂ) * u * g + (v + w * u) * f‖ ≤
        ‖(2 : ℂ) * u * g‖ + ‖(v + w * u) * f‖ :=
          norm_add_le _ _
    _ = 2 * (‖u‖ * ‖g‖) + ‖v + w * u‖ * ‖f‖ := by
      have hnormTwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      simp only [norm_mul, hnormTwo]
      ring
    _ ≤ 2 * ((C1 * A * ell) * (B * ell)) +
        (C2 * A ^ 2 * ell ^ 2 +
          (2 * A * ell) * (C1 * A * ell)) * B :=
      add_le_add
        (mul_le_mul_of_nonneg_left hfirst (by norm_num)) hsecond
    _ = (2 * C1 * A * B + (C2 + 2 * C1) * A ^ 2 * B) *
          ell ^ 2 := by ring

/-- A genuine C1 physical radiation sampled at ell*r has the
correct critical rescaling f_ell'=ell^(3/2)*z'(ell*r).
For 0<ell<=1 it has the derived extra spatial factor ell. -/
theorem actual_Hartree_physical_rescaled_first_radial_deriv_bound
    (ell r B : ℝ) (hell : 0 < ell) (hellSmall : ell ≤ 1)
    (hB : 0 ≤ B) (z : ℝ → ℂ)
    (hz : DifferentiableAt ℝ z (ell * r))
    (hzBound : ‖deriv z (ell * r)‖ ≤ B) :
    ‖deriv (rescalePhysicalRadiation ell z) r‖ ≤ B * ell := by
  have hS : Real.sqrt ell ≤ 1 := by
    simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt hellSmall)
  have hEq :
      ‖deriv (rescalePhysicalRadiation ell z) r‖ =
        Real.sqrt ell * ell * ‖deriv z (ell * r)‖ := by
    rw [actual_Hartree_critical_rescaled_radial_deriv ell r z hz]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg ell), abs_of_pos hell]
    ring
  calc
    ‖deriv (rescalePhysicalRadiation ell z) r‖ =
        Real.sqrt ell * ell * ‖deriv z (ell * r)‖ := hEq
    _ ≤ Real.sqrt ell * ell * B :=
      mul_le_mul_of_nonneg_left hzBound (by positivity)
    _ = Real.sqrt ell * (ell * B) := by ring
    _ ≤ 1 * (ell * B) :=
      mul_le_mul_of_nonneg_right hS (mul_nonneg hell.le hB)
    _ = B * ell := by ring

/-- The ENTIRE local radial-Laplacian moving-cutoff commutator of
the actual critical Hartree radiation has a source-level strict
positive gain 2beta-1, not merely bounds for an isolated cutoff.
-/
theorem actual_Hartree_full_spatial_cutoff_source_strict_gain
    (s ell m M C beta B r : ℝ)
    (hs : 1 ≤ s) (hell : 0 < ell) (hellSmall : ell ≤ 1)
    (hm : 0 < m) (hmBound : m ≤ M)
    (hC : 0 ≤ C) (hBeta : 1 / 2 < beta)
    (hTrap : ell ≤ C * s ^ (-beta))
    (hB : 0 ≤ B)
    (z : ℝ → ℂ)
    (hzSpace : ∀ x : ℝ, DifferentiableAt ℝ z (ell * x))
    (hzSecond : DifferentiableAt ℝ (deriv z) (ell * r))
    (hzBound : ‖z (ell * r)‖ ≤ B)
    (hzDerivBound : ‖deriv z (ell * r)‖ ≤ B)
    (hShell : actualHartreeMomentCutoffRadius ell m ≤ r) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      0 < actualPDEMomentCutoffGain beta ∧
      ‖complexRadialLaplacian
          (fun x =>
            actualOneLayerInnerOverlapCutoff
                (actualHartreeMomentCutoffRadius ell m) x *
              rescalePhysicalRadiation ell z x) r -
        actualOneLayerInnerOverlapCutoff
            (actualHartreeMomentCutoffRadius ell m) r *
          complexRadialLaplacian (rescalePhysicalRadiation ell z) r‖ ≤
        ((2 * C1 * (hartreeKappa * M / 4) * B +
          (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) *
          C ^ 2) * s ^ (-1 - actualPDEMomentCutoffGain beta) := by
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
  have hsqrt : Real.sqrt ell ≤ 1 := by
    simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt hellSmall)
  have hFSize : ‖f r‖ ≤ B := by
    dsimp [f, rescalePhysicalRadiation]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg ell)]
    calc
      Real.sqrt ell * ‖z (ell * r)‖ ≤ Real.sqrt ell * B :=
        mul_le_mul_of_nonneg_left hzBound (Real.sqrt_nonneg ell)
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hsqrt hB
      _ = B := by ring
  have hFder : ‖deriv f r‖ ≤ B * ell :=
    actual_Hartree_physical_rescaled_first_radial_deriv_bound
      ell r B hell hellSmall hB z (hzSpace r) hzDerivBound
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
          ell ^ 2 := by
    rw [hSource]
    exact radial_complex_commutator_norm_bound
      (deriv χ r) (deriv (deriv χ) r) ((2 : ℂ) / (r : ℂ))
      (f r) (deriv f r)
      C1 C2 A B ell hC1.le hC2.le hA hB hell.le
      hχ1 hχ2 hrCoef hFSize hFder
  have hEll2 :
      ell ^ 2 ≤ C ^ 2 * s ^ (-1 - actualPDEMomentCutoffGain beta) :=
    actual_PDE_trapped_length_squared_positive_gain
      s ell C beta hs hell.le hC hTrap
  have hCoeff : 0 ≤
      2 * C1 * A * B + (C2 + 2 * C1) * A ^ 2 * B := by positivity
  refine ⟨C1,C2,hC1,hC2,
    actual_PDE_moment_cutoff_gain_positive beta hBeta,?_⟩
  calc
    ‖complexRadialLaplacian (fun x => χ x * f x) r -
      χ r * complexRadialLaplacian f r‖ ≤
        (2 * C1 * A * B + (C2 + 2 * C1) * A ^ 2 * B) *
          ell ^ 2 := hNorm
    _ ≤ (2 * C1 * A * B + (C2 + 2 * C1) * A ^ 2 * B) *
          (C ^ 2 * s ^ (-1 - actualPDEMomentCutoffGain beta)) :=
        mul_le_mul_of_nonneg_left hEll2 hCoeff
    _ = ((2 * C1 * (hartreeKappa * M / 4) * B +
        (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) *
        C ^ 2) * s ^ (-1 - actualPDEMomentCutoffGain beta) := by
        dsimp [A]
        ring

end HBL.TypeIIDynamicSelection
