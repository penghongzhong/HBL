import HBL.RadialHartreeBubbleExact
import HBL.MonopoleHartreeExpansion

/-!
The same-object positive-half-line bridge between the actual radial
Hartree first variation and the constructed half-line `hPlusApply`.
The radial differential expression is `f'' + (2/r) f'`; its quotient
conjugation is proved from derivatives, not assumed as an equation.
This module makes no assertion about a three-dimensional radial lift.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The actual three-dimensional radial differential expression, restricted
here to positive scalar radii. No spatial lift is part of this definition. -/
def radialLaplacian (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv f) r + (2 / r) * deriv f r

/-- First quotient derivative at a positive radius. -/
theorem div_radius_hasDerivAt (q : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hq : DifferentiableAt ℝ q r) :
    HasDerivAt (fun x => q x / x) ((deriv q r * r - q r) / r ^ 2) r := by
  convert hq.hasDerivAt.div (hasDerivAt_id r) hr.ne' using 1
  · funext x
    rfl
  · simp only [id_eq, mul_one]

/-- The second quotient derivative is obtained from the first derivative
on a genuine neighborhood of the positive observation radius. -/
theorem div_radius_second_hasDerivAt (q : ℝ → ℝ)
    (hq : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ q x)
    {r : ℝ} (hr : 0 < r) (hq2 : DifferentiableAt ℝ (deriv q) r) :
    HasDerivAt (deriv (fun x => q x / x))
      ((deriv (deriv q) r * r * r ^ 2 -
        (deriv q r * r - q r) * (2 * r)) / (r ^ 2) ^ 2) r := by
  have hnum : HasDerivAt (fun x => deriv q x * x - q x)
      (deriv (deriv q) r * r) r := by
    convert (hq2.hasDerivAt.mul (hasDerivAt_id r)).sub (hq r hr).hasDerivAt using 1
    · funext x
      rfl
    · simp only [id_eq, mul_one]
      ring
  have hden : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    · funext x
      rfl
    · norm_num
  have hd := hnum.div hden (pow_ne_zero 2 hr.ne')
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with x hx
  exact (div_radius_hasDerivAt q hx (hq x hx)).deriv

/-- Exact quotient conjugation, with the required two derivatives proved
locally rather than a formal manipulation of totalized derivatives. -/
theorem radialLaplacian_div_radius (q : ℝ → ℝ)
    (hq : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ q x)
    {r : ℝ} (hr : 0 < r) (hq2 : DifferentiableAt ℝ (deriv q) r) :
    radialLaplacian (fun x => q x / x) r = deriv (deriv q) r / r := by
  unfold radialLaplacian
  rw [(div_radius_second_hasDerivAt q hq hr hq2).deriv,
    (div_radius_hasDerivAt q hr (hq r hr)).deriv]
  field_simp [hr.ne'] <;> ring

/-- Smooth cutoff multiplying the actual monopole. -/
def monopoleInnerCutoff (R r : ℝ) : ℝ := 1 - cutoff (r / R)

theorem monopoleInnerCutoff_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (monopoleInnerCutoff R) := by
  exact contDiff_const.sub
    (cutoff_contDiff_infty.comp (contDiff_id.div_const R))

theorem monopoleInnerProfile_differentiableAt {R r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (monopoleInnerProfile R) r := by
  have hb := (contDiff_infty_iff_deriv.mp (monopoleInnerCutoff_contDiff R)).1 r
  change DifferentiableAt ℝ (fun x => monopoleInnerCutoff R x * monopoleProfile x) r
  exact hb.mul (monopoleProfile_hasDerivAt hr).differentiableAt

theorem monopoleInnerProfile_deriv_differentiableAt {R r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (deriv (monopoleInnerProfile R)) r := by
  have hb1 := (contDiff_infty_iff_deriv.mp (monopoleInnerCutoff_contDiff R)).1
  have hb2 := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp (monopoleInnerCutoff_contDiff R)).2).1 r
  have hp1 := (monopoleProfile_hasDerivAt hr).differentiableAt
  have hp2 := (monopoleProfile_second_hasDerivAt hr).differentiableAt
  have hmodel := (hb2.hasDerivAt.mul hp1.hasDerivAt).add
    ((hb1 r).hasDerivAt.mul hp2.hasDerivAt)
  have he : deriv (monopoleInnerProfile R) =ᶠ[𝓝 r]
      (fun x => deriv (monopoleInnerCutoff R) x * monopoleProfile x +
        monopoleInnerCutoff R x * deriv monopoleProfile x) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    have hxder : HasDerivAt (monopoleInnerProfile R)
        (deriv (monopoleInnerCutoff R) x * monopoleProfile x +
          monopoleInnerCutoff R x * deriv monopoleProfile x) x := by
      change HasDerivAt (fun y => monopoleInnerCutoff R y * monopoleProfile y) _ x
      exact (hb1 x).hasDerivAt.mul (monopoleProfile_hasDerivAt hx).differentiableAt.hasDerivAt
    exact hxder.deriv
  exact (hmodel.congr_of_eventuallyEq he).differentiableAt

/-- Actual radial-profile regularity, available for subsequent differential
linearity on the same profile used in the nonlinear expansion. -/
theorem monopoleInnerRadialProfile_differentiableAt {R r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (monopoleInnerRadialProfile R) r := by
  exact (div_radius_hasDerivAt (monopoleInnerProfile R) hr
    (monopoleInnerProfile_differentiableAt hr)).differentiableAt

theorem monopoleInnerRadialProfile_deriv_differentiableAt {R r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (deriv (monopoleInnerRadialProfile R)) r := by
  exact (div_radius_second_hasDerivAt (monopoleInnerProfile R)
    (fun _ hx => monopoleInnerProfile_differentiableAt hx) hr
    (monopoleInnerProfile_deriv_differentiableAt hr)).differentiableAt

/-- The actual truncated radial profile, not a new independent `X`, has
the claimed quotient Laplacian at every positive radius. -/
theorem monopoleInnerRadialProfile_radialLaplacian {R r : ℝ} (hr : 0 < r) :
    radialLaplacian (monopoleInnerRadialProfile R) r =
      deriv (deriv (monopoleInnerProfile R)) r / r := by
  exact radialLaplacian_div_radius (monopoleInnerProfile R)
    (fun _ hx => monopoleInnerProfile_differentiableAt hx) hr
    (monopoleInnerProfile_deriv_differentiableAt hr)

theorem monopoleInnerProfile_eq_radius_mul {R r : ℝ} (hr : 0 < r) :
    monopoleInnerProfile R r = r * monopoleInnerRadialProfile R r := by
  unfold monopoleInnerRadialProfile
  field_simp [hr.ne']

/-- The actual nonlocal row is absolutely integrable, and its normalized
radial-potential identity holds with exactly one Hartree kappa factor. -/
theorem monopoleInnerProfile_nonlocal_radial_bridge {R r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun rho => hartreeKernel r rho * monopoleInnerProfile R rho) (Ioi 0) ∧
      nonlocalApply (monopoleInnerProfile R) r =
        4 * r * bubble r ^ 3 *
          radialHartreePotential (fun rho => bubble rho ^ 3 *
            monopoleInnerRadialProfile R rho) r := by
  let C := 8 * Real.pi * hartreeKappa * bubble r ^ 3
  let f : ℝ → ℝ := fun rho => rho * hartreeRadialLog r rho *
    (bubble rho ^ 3 * monopoleInnerRadialProfile R rho)
  have hrow : IntegrableOn f (Ioi 0) := (monopoleHartreeBaseLinear_control (R := R) hr).2.1
  have he : (fun rho => hartreeKernel r rho * monopoleInnerProfile R rho) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))] (fun rho => C * f rho) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    rw [monopoleInnerProfile_eq_radius_mul hrho]
    unfold hartreeKernel C f
    unfold hartreeRadialLog
    ring
  refine ⟨(hrow.const_mul C).congr he.symm, ?_⟩
  unfold nonlocalApply
  rw [integral_congr_ae he, integral_const_mul]
  unfold radialHartreePotential C f
  field_simp [hr.ne'] <;> ring

/-- The first variation is the actual one already used by the nonlinear
Taylor theorem, now normalized by the exact bubble-potential identity. -/
theorem monopoleRadialHartreeFirstVariation_conjugate {R r : ℝ} (hr : 0 < r) :
    r * monopoleRadialHartreeFirstVariation R r =
      9 * bubble r ^ 4 * monopoleInnerProfile R r +
        nonlocalApply (monopoleInnerProfile R) r := by
  rw [monopoleRadialHartreeFirstVariation,
    radialHartreePotential_bubble_four hr,
    (monopoleInnerProfile_nonlocal_radial_bridge (R := R) hr).2,
    monopoleInnerProfile_eq_radius_mul hr]
  ring

/-- The actual radial differential expression plus actual Hartree first
variation is exactly the negative conjugated `hPlusApply`. -/
theorem monopoleRadial_linearization_eq_hPlus {R r : ℝ} (hr : 0 < r) :
    radialLaplacian (monopoleInnerRadialProfile R) r +
        monopoleRadialHartreeFirstVariation R r =
      -hPlusApply (monopoleInnerProfile R) r / r := by
  have hV : potential r = 3 * bubble r ^ 4 := by
    unfold potential
    rw [show bubble r ^ 4 = (bubble r ^ 2) ^ 2 by ring, bubble_sq, inv_pow]
    ring
  have hfirst := monopoleRadialHartreeFirstVariation_conjugate (R := R) hr
  rw [monopoleInnerRadialProfile_radialLaplacian hr]
  unfold hPlusApply
  rw [hV]
  apply (eq_div_iff hr.ne').2
  field_simp [hr.ne']
  nlinarith [hfirst]

/-- On the fixed core the actual radial linearization has exactly the
already constructed monopole source and the genuine outer Hartree tail. -/
theorem monopoleRadial_linearization_core {R r : ℝ}
    (hR : 4 ≤ R) (hr : 0 < r) (hsep : r ≤ R / 2) :
    radialLaplacian (monopoleInnerRadialProfile R) r +
        monopoleRadialHartreeFirstVariation R r =
      -bubble r ^ 3 - nonlocalApply (monopoleOuterTail R) r / r := by
  rw [monopoleRadial_linearization_eq_hPlus hr,
    monopoleInnerProfile_hPlus_core hR hr hsep]
  unfold monopoleSource
  field_simp [hr.ne'] <;> ring

end HBL.Modulation.Monopole
