import HBL.TypeIIDynamicSelection.ActualHartreeFullMovingCutoffResidualSharp
import HBL.TypeIIDynamicSelection.ActualCutoffUniformTransport
import HBL.TypeIIDynamicSelection.ActualOneLayerSpatialOverlapGain
import Mathlib.Tactic

/-!
# Uniform cutoff constants for the complete physical Hartree moving shell

The existing complete shell theorem chose the three fixed-cutoff constants
inside each pointwise application.  Since the cutoff is a single globally
fixed smooth function, this file moves those constants in front of all
physical parameters.  This quantifier strengthening is needed before the
shell residual can be used as one time-dependent residual atom.

No PDE estimate is changed: material transport, radial Laplacian and the
full nonlocal Hartree commutator are exactly the already proved ones.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- A fixed global first-derivative cutoff bound gives the material shell
estimate for every radius and every modulation speed. -/
theorem actual_one_layer_material_transport_shell_bound_with_fixed_cutoff
    (Cchi : ℝ) (_hCchi : 0 < Cchi)
    (hCut : ∀ x : ℝ, |deriv cutoff x| ≤ Cchi)
    (radius radiusSpeed b r : ℝ)
    (hRadius : 0 < radius) (hrLeft : radius ≤ r)
    (hrRight : r ≤ 2 * radius) :
    |actualOneLayerMaterialCutoffCoefficient radius radiusSpeed b r| ≤
      2 * Cchi * |radiusSpeed / radius - b| := by
  have hrNonneg : 0 ≤ r / radius :=
    div_nonneg (le_trans hRadius.le hrLeft) hRadius.le
  have hrTwo : r / radius ≤ 2 := by
    apply (div_le_iff₀ hRadius).2
    linarith
  have hrEq :
      |actualOneLayerMaterialCutoffCoefficient radius radiusSpeed b r| =
        (r / radius) * |radiusSpeed / radius - b| *
          |deriv cutoff (r / radius)| := by
    unfold actualOneLayerMaterialCutoffCoefficient
    rw [abs_mul, abs_mul, abs_of_nonneg hrNonneg]
  rw [hrEq]
  have hP : 0 ≤ |radiusSpeed / radius - b| := abs_nonneg _
  calc
    (r / radius) * |radiusSpeed / radius - b| *
        |deriv cutoff (r / radius)| ≤
      (2 * |radiusSpeed / radius - b|) * Cchi := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hrTwo hP)
          (hCut (r / radius)) (abs_nonneg _) (by positivity)
    _ = 2 * Cchi * |radiusSpeed / radius - b| := by ring

private theorem uniform_radial_complex_commutator_norm_bound_sharp
    (u v w f g : ℂ) (C1 C2 A B ell : ℝ)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hell : 0 ≤ ell)
    (hu : ‖u‖ ≤ C1 * A * ell)
    (hv : ‖v‖ ≤ C2 * A ^ 2 * ell ^ 2)
    (hw : ‖w‖ ≤ 2 * A * ell)
    (hf : ‖f‖ ≤ Real.sqrt ell * B)
    (hg : ‖g‖ ≤ Real.sqrt ell * B * ell) :
    ‖(2 : ℂ) * u * g + (v + w * u) * f‖ ≤
      (2 * C1 * A * B + (C2 + 2 * C1) * A ^ 2 * B) *
        ell ^ 2 * Real.sqrt ell := by
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

/-- Fixed global C1/C2 cutoff constants give the physical Laplacian shell
estimate uniformly in all scale/moment/source parameters. -/
theorem actual_Hartree_full_spatial_cutoff_source_with_fixed_C2
    (C1 C2 : ℝ) (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hCut : ∀ R r : ℝ, 0 < R →
      ‖deriv (actualOneLayerInnerOverlapCutoff R) r‖ ≤ C1 / R ∧
      ‖deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r‖ ≤ C2 / R ^ 2)
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
  let R : ℝ := actualHartreeMomentCutoffRadius ell m
  let A : ℝ := hartreeKappa * M / 4
  let f : ℝ → ℂ := rescalePhysicalRadiation ell z
  let chi : ℝ → ℂ := actualOneLayerInnerOverlapCutoff R
  have hM : 0 < M := lt_of_lt_of_le hm hmBound
  have hA : 0 ≤ A := by
    dsimp [A]
    unfold hartreeKappa
    positivity
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
  have hchi1 : ‖deriv chi r‖ ≤ C1 * A * ell := by
    calc
      ‖deriv chi r‖ ≤ C1 / R := (hCut R r hR).1
      _ = C1 * (1 / R) := by field_simp [hR.ne']
      _ ≤ C1 * (A * ell) :=
        mul_le_mul_of_nonneg_left hRinv hC1.le
      _ = C1 * A * ell := by ring
  have hRInv2 : (1 / R) ^ 2 ≤ (A * ell) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hRinv 2
  have hchi2 : ‖deriv (deriv chi) r‖ ≤
      C2 * A ^ 2 * ell ^ 2 := by
    calc
      ‖deriv (deriv chi) r‖ ≤ C2 / R ^ 2 := (hCut R r hR).2
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
  have hchiSpace : ∀ x : ℝ, DifferentiableAt ℝ chi x :=
    fun x => (actual_one_layer_overlap_cutoff_hasDerivAt R x).differentiableAt
  have hchiSecond : DifferentiableAt ℝ (deriv chi) r :=
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
    chi f r hchiSpace hFSpace hchiSecond hFSecond
  rw [hSource]
  exact uniform_radial_complex_commutator_norm_bound_sharp
    (deriv chi r) (deriv (deriv chi) r) ((2 : ℂ) / (r : ℂ))
    (f r) (deriv f r)
    C1 C2 A B ell hC1.le hC2.le hA hB hell.le
    hchi1 hchi2 hrCoef hFSize hFder

/-- The complete true Hartree shell estimate with the same cutoff constants
for every choice of physical solution, scale and observation radius. -/
theorem actual_Hartree_full_physical_cutoff_PDE_shell_with_fixed_constants
    (Cchi C1 C2 : ℝ)
    (hCchi : 0 < Cchi) (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hCut1 : ∀ x : ℝ, |deriv cutoff x| ≤ Cchi)
    (hCut2 : ∀ R r : ℝ, 0 < R →
      ‖deriv (actualOneLayerInnerOverlapCutoff R) r‖ ≤ C1 / R ∧
      ‖deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r‖ ≤ C2 / R ^ 2)
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
    (hzQuartic : ∀ u : ℝ, 0 < u → ‖z u‖ ^ 4 ≤ D * bubble u ^ 2)
    (hShell : actualHartreeMomentCutoffRadius ell m ≤ r)
    (hShellRight : r ≤ 2 * actualHartreeMomentCutoffRadius ell m) :
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
  have hMat :=
    actual_one_layer_material_transport_shell_bound_with_fixed_cutoff
      Cchi hCchi hCut1 (R s) Rs b r hRpos hRleft hRright
  have hLoc :=
    actual_Hartree_full_spatial_cutoff_source_with_fixed_C2
      C1 C2 hC1 hC2 hCut2 ell m M B r hell hm hmBound hB z
      hzSpace hzSecond (hzAmp (ell * r) (mul_pos hell hr))
      hzDerivBound hShell
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
  have hNonlocal :=
    actual_Hartree_physical_nonlocal_cutoff_sharp_length_gain
      ell (R s) r B D hell hRpos hr hD hB z hz hzAmp hzQuartic
  have hRiesz :
      ‖complexRadialHartreeNonlinearity
        (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialHartreeNonlinearity (f s) r‖ ≤
      (2 * radialHartreeRowBoundConstant * D * B ^ 3) *
        ell ^ 2 * Real.sqrt ell := by
    rw [hfProfile]
    exact hNonlocal
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
  have hSource := actual_Hartree_full_moving_cutoff_residual_triangle
    R f b omega hR hRne hfTime hfSpace hf2 (r := r)
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

/-- The quantifier-strengthened complete shell theorem: one triple of cutoff
constants works for every physical application. -/
theorem actual_Hartree_full_physical_cutoff_PDE_shell_uniform_constants :
    ∃ Cchi C1 C2 : ℝ,
      0 < Cchi ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ (R : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
        (b omega : ℝ) (s r Rs ell m M B D : ℝ),
      ∀ (_hR : HasDerivAt R Rs s),
      ∀ (_hRadius : R s = actualHartreeMomentCutoffRadius ell m),
      ∀ (_hfTime : DifferentiableAt ℝ (fun t => f t r) s),
      ∀ (_hfSpace : ∀ x : ℝ, DifferentiableAt ℝ (f s) x),
      ∀ (_hf2 : DifferentiableAt ℝ (deriv (f s)) r),
      ∀ (_hell : 0 < ell), ∀ (_hm : 0 < m), ∀ (_hmBound : m ≤ M),
      ∀ (_hB : 0 ≤ B), ∀ (_hD : 0 ≤ D),
      ∀ (z : ℝ → ℂ), ∀ (_hz : Measurable z),
      ∀ (_hfProfile : f s = rescalePhysicalRadiation ell z),
      ∀ (_hzSpace : ∀ x : ℝ, DifferentiableAt ℝ z (ell * x)),
      ∀ (_hzSecond : DifferentiableAt ℝ (deriv z) (ell * r)),
      ∀ (_hzAmp : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B),
      ∀ (_hzDerivBound : ‖deriv z (ell * r)‖ ≤ B),
      ∀ (_hzQuartic : ∀ u : ℝ, 0 < u → ‖z u‖ ^ 4 ≤ D * bubble u ^ 2),
      ∀ (_hShell : actualHartreeMomentCutoffRadius ell m ≤ r),
      ∀ (_hShellRight : r ≤ 2 * actualHartreeMomentCutoffRadius ell m),
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
  obtain ⟨Cchi,hCchi,hCut1⟩ :=
    exists_actual_fixed_cutoff_uniform_deriv_bound
  obtain ⟨C1,C2,hC1,hC2,hCut2⟩ :=
    actual_Hartree_overlap_cutoff_uniform_C2_spatial_scaling
  refine ⟨Cchi,C1,C2,hCchi,hC1,hC2,?_⟩
  intro R f b omega s r Rs ell m M B D hR hRadius
    hfTime hfSpace hf2 hell hm hmBound hB hD z hz hfProfile
    hzSpace hzSecond hzAmp hzDerivBound hzQuartic hShell hShellRight
  exact actual_Hartree_full_physical_cutoff_PDE_shell_with_fixed_constants
    Cchi C1 C2 hCchi hC1 hC2 hCut1 hCut2
    R f b omega s r Rs ell m M B D hR hRadius
    hfTime hfSpace hf2 hell hm hmBound hB hD z hz hfProfile
    hzSpace hzSecond hzAmp hzDerivBound hzQuartic hShell hShellRight

end HBL.TypeIIDynamicSelection
