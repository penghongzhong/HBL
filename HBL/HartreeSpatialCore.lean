import HBL.RegularRadiationKernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Spatial derivatives of the actual inverse-square Hartree potential

This is a dense-core analytic bridge, not a new numbered manuscript result.
The kernel and potential are the original RegularRadiation definitions.
Derivatives transfer to the density, not to the singular kernel. The first
potential-derivative bound is independent of the compact support's radius.
The actual seventh-order nonlinearity is smooth on this spatial core and
its spatial product rule retains both nonlocal and local contributions.

Scope: compactly supported densities/fields. Extension to noncompact Sobolev
classes, differentiated remainder estimates and the physical constrained
evolution are NOT asserted here. Spatial smoothness is not a theorem about
Frechet smoothness of the nonlinear map between Sobolev spaces.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Topology

namespace HBL.RegularRadiation.SpatialCore

/-- The physical kernel with the complex codomain of the density. -/
def complexKernel (x : Space) : ℂ := (kernel x : ℂ)

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

/-- Finite and smooth differentiability orders transfer to the physical potential. -/
theorem potential_contDiff {n : ℕ∞} (ρ : Space → ℂ)
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ n ρ) :
    ContDiff ℝ n (potential ρ) := by
  rw [potential_eq_convolution]
  exact hc.contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) complexKernel_locallyIntegrable hρ

/-- The full real Frechet derivative, without differentiating the singular kernel. -/
theorem potential_hasFDerivAt (ρ : Space → ℂ)
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x : Space) :
    HasFDerivAt (potential ρ)
      (convolution complexKernel (fderiv ℝ ρ)
        ((ContinuousLinearMap.mul ℝ ℂ).precompR Space) volume x) x := by
  rw [potential_eq_convolution]
  exact hc.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) complexKernel_locallyIntegrable hρ x

/-- Directional derivatives are the actual potential of the differentiated density. -/
theorem potential_fderiv_apply (ρ : Space → ℂ)
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x v : Space) :
    fderiv ℝ (potential ρ) x v = potential (fun y => fderiv ℝ ρ y v) x := by
  rw [(potential_hasFDerivAt ρ hc hρ x).fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    complexKernel_locallyIntegrable (hc.fderiv ℝ)
    (hρ.continuous_fderiv (by norm_num)) x v]
  rw [potential_eq_convolution]

/-- Support-independent first spatial derivative bound. Density-derivative
integrability and the derivative identity are derived, not assumed. -/
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
      _ ≤ ∫ y : Space, ‖fderiv ℝ ρ y v‖ := le_rfl
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
      add_le_add le_rfl hI
    _ = (nearMass * M + ∫ y : Space, ‖fderiv ℝ ρ y‖) * ‖v‖ := by ring

private theorem density_contDiff {n : ℕ∞} (f : Space → ℂ)
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (quarticDensity f) := by
  have he : quarticDensity f = fun y => (((‖f y‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
    funext y
    unfold quarticDensity
    congr 1
    ring
  rw [he]
  exact Complex.ofRealCLM.contDiff.comp ((hf.norm_sq ℂ).pow 2)

private theorem density_compact (f : Space → ℂ) (hc : HasCompactSupport f) :
    HasCompactSupport (quarticDensity f) := by
  apply HasCompactSupport.of_support_subset_isCompact hc.isCompact
  intro x hx
  by_contra hn
  exact hx (by simp [quarticDensity, image_eq_zero_of_notMem_tsupport hn])

private theorem cubic_contDiff {n : ℕ∞} (f : Space → ℂ) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun y => (((‖f y‖ ^ 2 : ℝ) : ℂ) * f y)) :=
  (Complex.ofRealCLM.contDiff.comp (hf.norm_sq ℂ)).mul hf

/-- Spatial regularity of the original seventh-order Hartree expression on its core. -/
theorem hartree_contDiff_core {n : ℕ∞} (κ : ℝ) (f : Space → ℂ)
    (hc : HasCompactSupport f) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (hartreeNonlinearity κ f) := by
  have hP := potential_contDiff (quarticDensity f) (density_compact f hc) (density_contDiff f hf)
  exact (contDiff_const.mul hP).mul (cubic_contDiff f hf)

/-- Exact spatial product rule for the actual Hartree nonlinearity. The nonlocal
term is the original convolution of the actual quartic density derivative. -/
theorem hartree_fderiv_core (κ : ℝ) (f : Space → ℂ)
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (x v : Space) :
    fderiv ℝ (hartreeNonlinearity κ f) x v =
      (κ : ℂ) *
        (potential (fun y => fderiv ℝ (quarticDensity f) y v) x *
            (((‖f x‖ ^ 2 : ℝ) : ℂ) * f x) +
          potential (quarticDensity f) x *
            fderiv ℝ (fun y => (((‖f y‖ ^ 2 : ℝ) : ℂ) * f y)) x v) := by
  let C : Space → ℂ := fun y => (((‖f y‖ ^ 2 : ℝ) : ℂ) * f y)
  have hC : ContDiff ℝ 1 C := cubic_contDiff f hf
  have hρ : ContDiff ℝ 1 (quarticDensity f) := density_contDiff f hf
  have hcρ := density_compact f hc
  have hP := potential_contDiff (quarticDensity f) hcρ hρ
  have hd := ((hP.differentiable (by norm_num) x).hasFDerivAt.const_mul (κ : ℂ)).mul
    ((hC.differentiable (by norm_num) x).hasFDerivAt)
  have he : fderiv ℝ (hartreeNonlinearity κ f) x =
      ((κ : ℂ) * potential (quarticDensity f) x) • fderiv ℝ C x +
        C x • ((κ : ℂ) • fderiv ℝ (potential (quarticDensity f)) x) := hd.fderiv
  rw [he]
  change ((κ : ℂ) * potential (quarticDensity f) x) * (fderiv ℝ C x v) +
    C x * ((κ : ℂ) * (fderiv ℝ (potential (quarticDensity f)) x v)) = _
  rw [potential_fderiv_apply (quarticDensity f) hcρ hρ x v]
  dsimp [C]
  ring

#print axioms complexKernel_locallyIntegrable
#print axioms potential_eq_convolution
#print axioms potential_contDiff
#print axioms potential_hasFDerivAt
#print axioms potential_fderiv_apply
#print axioms potential_fderiv_bound
#print axioms hartree_contDiff_core
#print axioms hartree_fderiv_core

end HBL.RegularRadiation.SpatialCore
