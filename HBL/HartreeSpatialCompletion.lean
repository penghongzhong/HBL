import HBL.HartreeSpatialCore
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Noncompact completion of the physical Hartree potential derivative

The operator-valued convolution below is the actual inverse-square integral.
Its integrability and bounds are proved from the existing scalar kernel estimate.
The terminal theorem assumes approximation of the DENSITY and its gradient in
L1 and essential supremum norms, not differentiability of the limiting potential.
It proves that differentiability by uniform convergence of the actual convolutions.

No compact support is imposed on the limiting density or gradient. Construction
of the required approximants for the final Hartree Sobolev source class, nonlinear
remainder derivative bounds, and the constrained evolution are separate obligations.
This is one analytic source-completion bridge, not a new numbered paper environment.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology

namespace HBL.RegularRadiation.SpatialCompletion

open SpatialCore

/-- The actual operator-valued potential of a density gradient. -/
def gradientPotential (D : Space → Space →L[ℝ] ℂ) (x : Space) : Space →L[ℝ] ℂ :=
  ∫ y : Space, (kernel (x - y) : ℂ) • D y

/-- Noncompact L1/L-infinity gradient fields produce absolutely convergent
operator-valued convolutions with a support-independent norm bound. -/
theorem gradientPotential_bound (D : Space → Space →L[ℝ] ℂ)
    (hD : Integrable D) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ y : Space, ‖D y‖ ≤ M) (x : Space) :
    Integrable (fun y : Space => (kernel (x - y) : ℂ) • D y) ∧
      ‖gradientPotential D x‖ ≤ nearMass * M + ∫ y : Space, ‖D y‖ := by
  have hbρ : ∀ᵐ y : Space, ‖(‖D y‖ : ℂ)‖ ≤ M := by
    filter_upwards [hb] with y hy
    simpa only [Complex.norm_real, norm_norm] using hy
  have hs := potential_bound (fun y : Space => (‖D y‖ : ℂ))
    hD.norm.ofReal M hM hbρ x
  have hk : Measurable (fun y : Space => (kernel (x - y) : ℂ)) := by
    unfold kernel
    fun_prop
  have hn (y : Space) :
      ‖(kernel (x - y) : ℂ) • D y‖ =
        ‖(kernel (x - y) : ℂ) * (‖D y‖ : ℂ)‖ := by
    simp only [norm_smul, norm_mul, Complex.norm_real, norm_norm]
  have hi : Integrable (fun y : Space => (kernel (x - y) : ℂ) • D y) := by
    apply hs.1.norm.mono' (hk.aestronglyMeasurable.smul hD.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun y => (hn y).le)
  have hkpos (y : Space) : 0 ≤ kernel (x - y) := by
    unfold kernel
    positivity
  have hreal : potential (fun y : Space => (‖D y‖ : ℂ)) x =
      ((∫ y : Space, kernel (x - y) * ‖D y‖ : ℝ) : ℂ) := by
    unfold potential
    simp_rw [← Complex.ofReal_mul]
    exact integral_ofReal
  have hbound := hs.2
  rw [hreal, Complex.norm_real, Real.norm_of_nonneg
    (integral_nonneg (fun y => mul_nonneg (hkpos y) (norm_nonneg (D y))))] at hbound
  simp only [Complex.norm_real, norm_norm] at hbound
  refine ⟨hi, ?_⟩
  calc
    ‖gradientPotential D x‖ ≤ ∫ y : Space, ‖(kernel (x - y) : ℂ) • D y‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : Space, kernel (x - y) * ‖D y‖ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hkpos y)]
    _ ≤ nearMass * M + ∫ y : Space, ‖D y‖ := hbound

/-- Evaluation commutes with the genuinely integrable operator-valued potential. -/
theorem gradientPotential_apply (D : Space → Space →L[ℝ] ℂ)
    (hD : Integrable D) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ y : Space, ‖D y‖ ≤ M) (x v : Space) :
    gradientPotential D x v = potential (fun y => D y v) x := by
  unfold gradientPotential
  rw [ContinuousLinearMap.integral_apply (gradientPotential_bound D hD M hM hb x).1]
  unfold potential
  apply integral_congr_ae
  filter_upwards with y
  rfl

/-- The operator-valued source difference estimate, without support assumptions. -/
theorem gradientPotential_difference_bound
    (D E : Space → Space →L[ℝ] ℂ) (hD : Integrable D) (hE : Integrable E)
    (MD ME e : ℝ) (hMD : 0 ≤ MD) (hME : 0 ≤ ME) (he : 0 ≤ e)
    (hDb : ∀ᵐ y : Space, ‖D y‖ ≤ MD) (hEb : ∀ᵐ y : Space, ‖E y‖ ≤ ME)
    (hde : ∀ᵐ y : Space, ‖D y - E y‖ ≤ e) (x : Space) :
    ‖gradientPotential D x - gradientPotential E x‖ ≤
      nearMass * e + ∫ y : Space, ‖D y - E y‖ := by
  have hsplit : gradientPotential (fun y => D y - E y) x =
      gradientPotential D x - gradientPotential E x := by
    unfold gradientPotential
    simp_rw [smul_sub]
    exact integral_sub (gradientPotential_bound D hD MD hMD hDb x).1
      (gradientPotential_bound E hE ME hME hEb x).1
  have h := (gradientPotential_bound (fun y => D y - E y) (hD.sub hE) e he hde x).2
  rw [hsplit] at h
  exact h

/-- Identify the core derivative with the noncompact operator-valued realization. -/
theorem potential_core_gradient (ρ : Space → ℂ)
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ y : Space, ‖fderiv ℝ ρ y‖ ≤ M) (x : Space) :
    HasFDerivAt (potential ρ) (gradientPotential (fderiv ℝ ρ) x) x := by
  have hDi : Integrable (fderiv ℝ ρ) :=
    (hρ.continuous_fderiv (by norm_num)).integrable_of_hasCompactSupport (hc.fderiv ℝ)
  have heq : fderiv ℝ (potential ρ) x = gradientPotential (fderiv ℝ ρ) x := by
    ext v
    rw [potential_fderiv_apply ρ hc hρ x v,
      gradientPotential_apply (fderiv ℝ ρ) hDi M hM hb x v]
  rw [← heq]
  exact ((potential_contDiff ρ hc hρ).differentiable (by norm_num) x).hasFDerivAt

/-- Actual noncompact derivative realization from compact-core source approximation.
All convergence hypotheses concern the density and its gradients BEFORE convolution.
No convergence, derivative identity, or bound for the limiting potential is assumed. -/
theorem potential_hasFDerivAt_of_core_approximation
    (ρ : Space → ℂ) (D : Space → Space →L[ℝ] ℂ)
    (ρn : ℕ → Space → ℂ)
    (hc : ∀ n, HasCompactSupport (ρn n))
    (hn : ∀ n, ContDiff ℝ 1 (ρn n))
    (hρ : Integrable ρ) (hD : Integrable D)
    (M0 M1 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hb0 : ∀ᵐ y : Space, ‖ρ y‖ ≤ M0)
    (hb1 : ∀ᵐ y : Space, ‖D y‖ ≤ M1)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (he0 : ∀ n, ∀ᵐ y : Space, ‖ρn n y - ρ y‖ ≤ ε n)
    (he1 : ∀ n, ∀ᵐ y : Space, ‖fderiv ℝ (ρn n) y - D y‖ ≤ ε n)
    (hi0 : ∀ n, (∫ y : Space, ‖ρn n y - ρ y‖) ≤ ε n)
    (hi1 : ∀ n, (∫ y : Space, ‖fderiv ℝ (ρn n) y - D y‖) ≤ ε n) :
    ∀ x : Space, HasFDerivAt (potential ρ) (gradientPotential D x) x := by
  have hni (n : ℕ) : Integrable (ρn n) :=
    (hn n).continuous.integrable_of_hasCompactSupport (hc n)
  have hnDi (n : ℕ) : Integrable (fderiv ℝ (ρn n)) :=
    ((hn n).continuous_fderiv (by norm_num)).integrable_of_hasCompactSupport ((hc n).fderiv ℝ)
  have hnb0 (n : ℕ) : ∀ᵐ y : Space, ‖ρn n y‖ ≤ M0 + ε n := by
    filter_upwards [hb0, he0 n] with y hy he
    have h := norm_le_norm_sub_add (ρn n y) (ρ y)
    linarith
  have hnb1 (n : ℕ) : ∀ᵐ y : Space, ‖fderiv ℝ (ρn n) y‖ ≤ M1 + ε n := by
    filter_upwards [hb1, he1 n] with y hy he
    have h := norm_le_norm_sub_add (fderiv ℝ (ρn n) y) (D y)
    linarith
  have hval (n : ℕ) (x : Space) :
      ‖potential (ρn n) x - potential ρ x‖ ≤ (nearMass + 1) * ε n := by
    calc
      _ ≤ nearMass * ε n + ∫ y : Space, ‖ρn n y - ρ y‖ :=
        potential_sub_bound (ρn n) ρ (hni n) hρ (M0 + ε n) M0 (ε n)
          (add_nonneg hM0 (hε n)) hM0 (hε n) (hnb0 n) hb0 (he0 n) x
      _ ≤ nearMass * ε n + ε n := add_le_add le_rfl (hi0 n)
      _ = (nearMass + 1) * ε n := by ring
  have hgrad (n : ℕ) (x : Space) :
      ‖gradientPotential (fderiv ℝ (ρn n)) x - gradientPotential D x‖ ≤
        (nearMass + 1) * ε n := by
    calc
      _ ≤ nearMass * ε n + ∫ y : Space, ‖fderiv ℝ (ρn n) y - D y‖ :=
        gradientPotential_difference_bound (fderiv ℝ (ρn n)) D (hnDi n) hD
          (M1 + ε n) M1 (ε n) (add_nonneg hM1 (hε n)) hM1 (hε n)
          (hnb1 n) hb1 (he1 n) x
      _ ≤ nearMass * ε n + ε n := add_le_add le_rfl (hi1 n)
      _ = (nearMass + 1) * ε n := by ring
  have ht : Tendsto (fun n => (nearMass + 1) * ε n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hεlim
  have huv : TendstoUniformly (fun n => potential (ρn n)) (potential ρ) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro e he
    filter_upwards [(tendsto_order.1 ht).2 e he] with n hnlt x
    calc
      dist (potential ρ x) (potential (ρn n) x) =
          ‖potential (ρn n) x - potential ρ x‖ := by rw [dist_comm, dist_eq_norm]
      _ ≤ (nearMass + 1) * ε n := hval n x
      _ < e := hnlt
  have hug : TendstoUniformly (fun n => gradientPotential (fderiv ℝ (ρn n)))
      (gradientPotential D) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro e he
    filter_upwards [(tendsto_order.1 ht).2 e he] with n hnlt x
    calc
      dist (gradientPotential D x) (gradientPotential (fderiv ℝ (ρn n)) x) =
          ‖gradientPotential (fderiv ℝ (ρn n)) x - gradientPotential D x‖ := by
            rw [dist_comm, dist_eq_norm]
      _ ≤ (nearMass + 1) * ε n := hgrad n x
      _ < e := hnlt
  exact hasFDerivAt_of_tendstoUniformly hug
    (fun n x => potential_core_gradient (ρn n) (hc n) (hn n)
      (M1 + ε n) (add_nonneg hM1 (hε n)) (hnb1 n) x)
    (fun x => huv.tendsto_at x)

#print axioms gradientPotential
#print axioms gradientPotential_bound
#print axioms gradientPotential_apply
#print axioms gradientPotential_difference_bound
#print axioms potential_core_gradient
#print axioms potential_hasFDerivAt_of_core_approximation

end HBL.RegularRadiation.SpatialCompletion
