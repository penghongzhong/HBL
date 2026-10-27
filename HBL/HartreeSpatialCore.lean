import HBL.RegularRadiationKernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Spatial derivatives of the actual inverse-square Hartree potential

This is a dense-core analytic bridge, not a new numbered manuscript result.
The kernel is exactly `RegularRadiation.kernel` and the potential is exactly
`RegularRadiation.potential`. We transfer derivatives to the density, rather
than differentiating the singular kernel. The first-derivative operator-norm
bound is independent of the compact support's radius.

Scope: C1 compactly supported complex densities. Extension to noncompact
Sobolev densities, the full differentiated nonlinear remainder, and the
physical constrained evolution are NOT asserted by this file.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Topology

namespace HBL.RegularRadiation.SpatialCore

/-- The physical inverse-square kernel with the complex codomain of the density. -/
def complexKernel (x : Space) : ℂ := (kernel x : ℂ)

/-- Local integrability is proved for the actual three-dimensional kernel. -/
theorem complexKernel_locallyIntegrable : LocallyIntegrable complexKernel := by
  apply locallyIntegrable_of_norm_le_rpow
    (C := 1) (α := 2) (by norm_num [Space]) (by norm_num [Space])
  · filter_upwards with x
    simp only [complexKernel, kernel, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ (‖x‖ ^ 2)⁻¹), one_mul]
    rw [Real.rpow_neg (norm_nonneg x), Real.rpow_two]
  · have hm : Measurable complexKernel := by
      unfold complexKernel kernel
      fun_prop
    exact hm.aestronglyMeasurable

/-- Identify the pre-existing physical potential with Mathlib's convolution. -/
theorem potential_eq_convolution (ρ : Space → ℂ) :
    potential ρ = convolution complexKernel ρ (ContinuousLinearMap.mul ℝ ℂ) volume := by
  funext x
  rw [convolution_eq_swap]
  rfl

/-- All finite differentiability orders transfer to the actual potential on the core. -/
theorem potential_contDiff {n : ℕ∞} (ρ : Space → ℂ)
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ n ρ) :
    ContDiff ℝ n (potential ρ) := by
  rw [potential_eq_convolution]
  exact hc.contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) complexKernel_locallyIntegrable hρ

/-- The full real Frechet derivative; no derivative of the singular kernel occurs. -/
theorem potential_hasFDerivAt (ρ : Space → ℂ)
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x : Space) :
    HasFDerivAt (potential ρ)
      (convolution complexKernel (fderiv ℝ ρ)
        ((ContinuousLinearMap.mul ℝ ℂ).precompR Space) volume x) x := by
  rw [potential_eq_convolution]
  exact hc.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) complexKernel_locallyIntegrable hρ x

/-- Every directional derivative is the same physical potential of the density derivative. -/
theorem potential_fderiv_apply (ρ : Space → ℂ)
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x v : Space) :
    fderiv ℝ (potential ρ) x v = potential (fun y => fderiv ℝ ρ y v) x := by
  rw [(potential_hasFDerivAt ρ hc hρ x).fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    complexKernel_locallyIntegrable (hc.fderiv ℝ)
    (hρ.continuous_fderiv (by norm_num)) x v]
  rw [potential_eq_convolution]

/-- A support-independent first spatial derivative bound for the physical kernel.
Both derivative integrability and the actual derivative identity are derived.
Only an L-infinity bound of the input density derivative is supplied. -/
theorem potential_fderiv_bound (ρ : Space → ℂ)
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ y : Space, ‖fderiv ℝ ρ y‖ ≤ M) (x : Space) :
    Integrable (fderiv ℝ ρ) ∧
      ‖fderiv ℝ (potential ρ) x‖ ≤
        nearMass * M + ∫ y : Space, ‖fderiv ℝ ρ y‖ := by
  have hdcont : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv (by norm_num)
  have hDi : Integrable (fderiv ℝ ρ) :=
    hdcont.integrable_of_hasCompactSupport (hc.fderiv ℝ)
  refine ⟨hDi, ?_⟩
  have hnear : 0 ≤ nearMass := regularRadiationKernel_checks.2.1
  have hnon : 0 ≤ nearMass * M + ∫ y : Space, ‖fderiv ℝ ρ y‖ :=
    add_nonneg (mul_nonneg hnear hM) (integral_nonneg (fun y => norm_nonneg _))
  apply ContinuousLinearMap.opNorm_le_bound _ hnon
  intro v
  have hdircont : Continuous (fun y : Space => fderiv ℝ ρ y v) :=
    hdcont.clm_apply continuous_const
  have hdir : Integrable (fun y : Space => fderiv ℝ ρ y v) := by
    apply (hDi.norm.mul_const ‖v‖).mono' hdircont.aestronglyMeasurable
    filter_upwards with y
    exact (fderiv ℝ ρ y).le_opNorm v
  have hbdir : ∀ᵐ y : Space, ‖fderiv ℝ ρ y v‖ ≤ M * ‖v‖ := by
    filter_upwards [hb] with y hy
    exact ((fderiv ℝ ρ y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hy (norm_nonneg v))
  have hI : (∫ y : Space, ‖fderiv ℝ ρ y v‖) ≤
      (∫ y : Space, ‖fderiv ℝ ρ y‖) * ‖v‖ := by
    calc
      _ ≤ ∫ y : Space, ‖fderiv ℝ ρ y‖ * ‖v‖ := by
        apply integral_mono_ae hdir.norm (hDi.norm.mul_const ‖v‖)
        filter_upwards with y
        exact (fderiv ℝ ρ y).le_opNorm v
      _ = _ := integral_mul_const _ _
  rw [potential_fderiv_apply ρ hc hρ x v]
  calc
    _ ≤ nearMass * (M * ‖v‖) + ∫ y : Space, ‖fderiv ℝ ρ y v‖ :=
      (potential_bound (fun y => fderiv ℝ ρ y v) hdir
        (M * ‖v‖) (mul_nonneg hM (norm_nonneg v)) hbdir x).2
    _ ≤ nearMass * (M * ‖v‖) + (∫ y : Space, ‖fderiv ℝ ρ y‖) * ‖v‖ :=
      add_le_add_left hI _
    _ = (nearMass * M + ∫ y : Space, ‖fderiv ℝ ρ y‖) * ‖v‖ := by ring

#print axioms complexKernel_locallyIntegrable
#print axioms potential_eq_convolution
#print axioms potential_contDiff
#print axioms potential_hasFDerivAt
#print axioms potential_fderiv_apply
#print axioms potential_fderiv_bound

end HBL.RegularRadiation.SpatialCore
