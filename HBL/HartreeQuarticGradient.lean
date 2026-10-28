import HBL.HartreeSpatialCompletion

/-!
# Actual quartic-density gradients without a background L2 assumption

This file discharges the density/gradient integrability and boundedness inputs
of HartreeSpatialCompletion from actual field data. The field is C1, in L4 and
bounded; its spatial derivative is in L2 and bounded. No compact support or L2
membership of the field is required. Thus the scope includes a non-L2 background
provided the displayed field bounds have been established for it.

The last theorem is still conditional on compact-core approximation of the
actual density and its actual gradient. It does not construct that approximation,
the physical constrained propagator, or the full high-regularity local theory.
No original numbered manuscript environment is newly accepted by this file.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology

namespace HBL.RegularRadiation.QuarticGradient

open SpatialCompletion

/-- Spatial C1 regularity of the actual quartic density, with no support condition. -/
theorem quarticDensity_contDiff (f : Space → ℂ) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (quarticDensity f) := by
  have he : quarticDensity f = fun y => (((‖f y‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
    funext y
    unfold quarticDensity
    congr 1
    ring
  rw [he]
  exact Complex.ofRealCLM.contDiff.comp ((hf.norm_sq ℂ).pow 2)

/-- The exact real differential of the physical quartic density. -/
theorem quarticDensity_fderiv_apply (f : Space → ℂ) {x : Space}
    (hf : DifferentiableAt ℝ f x) (v : Space) :
    fderiv ℝ (quarticDensity f) x v =
      ((4 * ‖f x‖ ^ 2 * inner ℝ (f x) (fderiv ℝ f x v) : ℝ) : ℂ) := by
  have he : quarticDensity f = fun y => Complex.ofRealCLM ((‖f y‖ ^ 2) ^ 2) := by
    funext y
    change ((‖f y‖ ^ 4 : ℝ) : ℂ) = (((‖f y‖ ^ 2) ^ 2 : ℝ) : ℂ)
    congr 1
    ring
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x (hf.hasFDerivAt.norm_sq.pow 2)
  rw [he, hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul, pow_one,
    Nat.cast_ofNat, Nat.reduceSub, Complex.ofRealCLM_apply, innerSL_apply]
  congr 1
  ring

/-- The gradient estimate retains the cubic field factor needed for L1 control. -/
theorem quarticDensity_fderiv_norm_le (f : Space → ℂ) {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (quarticDensity f) x‖ ≤
      4 * ‖f x‖ ^ 3 * ‖fderiv ℝ f x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [quarticDensity_fderiv_apply f hf v, Complex.norm_real, Real.norm_eq_abs]
  have hip : |inner ℝ (f x) (fderiv ℝ f x v)| ≤
      ‖f x‖ * ‖fderiv ℝ f x v‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) (f x) (fderiv ℝ f x v))
  calc
    _ = (4 * ‖f x‖ ^ 2) * |inner ℝ (f x) (fderiv ℝ f x v)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * ‖f x‖ ^ 2)]
    _ ≤ (4 * ‖f x‖ ^ 2) * (‖f x‖ * ‖fderiv ℝ f x v‖) :=
      mul_le_mul_of_nonneg_left hip (by positivity)
    _ ≤ (4 * ‖f x‖ ^ 2) * (‖f x‖ * (‖fderiv ℝ f x‖ * ‖v‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((fderiv ℝ f x).le_opNorm v) (norm_nonneg _))
        (by positivity)
    _ = (4 * ‖f x‖ ^ 3 * ‖fderiv ℝ f x‖) * ‖v‖ := by ring

/-- Actual density and gradient are in L1, with quantitative gradient mass.
This derives L6 from L4 and the displayed bound rather than assuming field L2. -/
theorem quarticDensity_gradient_source
    (f : Space → ℂ) (hf : ContDiff ℝ 1 f)
    (h4 : Integrable (fun y : Space => ‖f y‖ ^ 4))
    (hd : MemLp (fderiv ℝ f) 2)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hfb : ∀ᵐ y : Space, ‖f y‖ ≤ M)
    (hdb : ∀ᵐ y : Space, ‖fderiv ℝ f y‖ ≤ L) :
    Integrable (quarticDensity f) ∧
    Integrable (fderiv ℝ (quarticDensity f)) ∧
    (∫ y : Space, ‖fderiv ℝ (quarticDensity f) y‖) ≤
      2 * (M ^ 2 * (∫ y : Space, ‖f y‖ ^ 4) +
        ∫ y : Space, ‖fderiv ℝ f y‖ ^ 2) ∧
    (∀ᵐ y : Space, ‖fderiv ℝ (quarticDensity f) y‖ ≤ 4 * M ^ 3 * L) := by
  have h6dom : ∀ᵐ y : Space, ‖‖f y‖ ^ 6‖ ≤ M ^ 2 * ‖f y‖ ^ 4 := by
    filter_upwards [hfb] with y hy
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 6)]
    calc
      _ = ‖f y‖ ^ 2 * ‖f y‖ ^ 4 := by ring
      _ ≤ M ^ 2 * ‖f y‖ ^ 4 := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hy 2) (by positivity)
  have h6 : Integrable (fun y : Space => ‖f y‖ ^ 6) :=
    (h4.const_mul (M ^ 2)).mono' (hf.continuous.aestronglyMeasurable.norm.pow 6) h6dom
  have hI6 : (∫ y : Space, ‖f y‖ ^ 6) ≤ M ^ 2 * (∫ y : Space, ‖f y‖ ^ 4) := by
    have hi := integral_mono_ae h6 (h4.const_mul (M ^ 2))
      (h6dom.mono fun y hy => by
        simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 6)] using hy)
    rwa [integral_const_mul] at hi
  have hgrad2 := hd.norm.integrable_sq
  have hdom : ∀ᵐ y : Space, ‖fderiv ℝ (quarticDensity f) y‖ ≤
      2 * (‖f y‖ ^ 6 + ‖fderiv ℝ f y‖ ^ 2) := by
    filter_upwards with y
    apply (quarticDensity_fderiv_norm_le f (hf.differentiable (by norm_num) y)).trans
    nlinarith only [sq_nonneg (‖f y‖ ^ 3 - ‖fderiv ℝ f y‖)]
  have hDρ : Integrable (fderiv ℝ (quarticDensity f)) :=
    ((h6.add hgrad2).const_mul 2).mono'
      ((quarticDensity_contDiff f hf).continuous_fderiv (by norm_num)).aestronglyMeasurable hdom
  have hI : (∫ y : Space, ‖fderiv ℝ (quarticDensity f) y‖) ≤
      2 * ((∫ y : Space, ‖f y‖ ^ 6) + ∫ y : Space, ‖fderiv ℝ f y‖ ^ 2) := by
    have hi := integral_mono_ae hDρ.norm ((h6.add hgrad2).const_mul 2) hdom
    rwa [integral_const_mul, integral_add h6 hgrad2] at hi
  refine ⟨h4.ofReal, hDρ, ?_, ?_⟩
  · exact hI.trans (mul_le_mul_of_nonneg_left (add_le_add hI6 le_rfl) (by norm_num))
  · filter_upwards [hfb, hdb] with y hy hdy
    apply (quarticDensity_fderiv_norm_le f (hf.differentiable (by norm_num) y)).trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy 3) (by norm_num))
      hdy (norm_nonneg _) (by positivity)

/-- The constructed noncompact gradient convolution of the ACTUAL density is
absolutely convergent and quantitatively bounded from field data alone. -/
theorem quarticDensity_gradient_potential_bound
    (f : Space → ℂ) (hf : ContDiff ℝ 1 f)
    (h4 : Integrable (fun y : Space => ‖f y‖ ^ 4))
    (hd : MemLp (fderiv ℝ f) 2)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hfb : ∀ᵐ y : Space, ‖f y‖ ≤ M)
    (hdb : ∀ᵐ y : Space, ‖fderiv ℝ f y‖ ≤ L) (x : Space) :
    Integrable (fun y : Space => (kernel (x - y) : ℂ) • fderiv ℝ (quarticDensity f) y) ∧
    ‖gradientPotential (fderiv ℝ (quarticDensity f)) x‖ ≤
      nearMass * (4 * M ^ 3 * L) +
        2 * (M ^ 2 * (∫ y : Space, ‖f y‖ ^ 4) +
          ∫ y : Space, ‖fderiv ℝ f y‖ ^ 2) := by
  obtain ⟨_, hDρ, hI, hb⟩ := quarticDensity_gradient_source f hf h4 hd M L hM hL hfb hdb
  have h := gradientPotential_bound (fderiv ℝ (quarticDensity f)) hDρ
    (4 * M ^ 3 * L) (by positivity) hb x
  exact ⟨h.1, h.2.trans (add_le_add le_rfl hI)⟩

/-- Specialize the completion theorem to the actual quartic density. Its L1 and
L-infinity inputs are now proved from the field, not extra density assumptions.
The compact-core approximation itself remains explicit and unconstructed here. -/
theorem quarticPotential_derivative_of_core_approximation
    (f : Space → ℂ) (hf : ContDiff ℝ 1 f)
    (h4 : Integrable (fun y : Space => ‖f y‖ ^ 4))
    (hd : MemLp (fderiv ℝ f) 2)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hfb : ∀ᵐ y : Space, ‖f y‖ ≤ M)
    (hdb : ∀ᵐ y : Space, ‖fderiv ℝ f y‖ ≤ L)
    (ρn : ℕ → Space → ℂ) (hc : ∀ n, HasCompactSupport (ρn n))
    (hn : ∀ n, ContDiff ℝ 1 (ρn n))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (he0 : ∀ n, ∀ᵐ y : Space, ‖ρn n y - quarticDensity f y‖ ≤ ε n)
    (he1 : ∀ n, ∀ᵐ y : Space,
      ‖fderiv ℝ (ρn n) y - fderiv ℝ (quarticDensity f) y‖ ≤ ε n)
    (hi0 : ∀ n, (∫ y : Space, ‖ρn n y - quarticDensity f y‖) ≤ ε n)
    (hi1 : ∀ n, (∫ y : Space,
      ‖fderiv ℝ (ρn n) y - fderiv ℝ (quarticDensity f) y‖) ≤ ε n) :
    ∀ x : Space, HasFDerivAt (potential (quarticDensity f))
      (gradientPotential (fderiv ℝ (quarticDensity f)) x) x := by
  obtain ⟨hρ, hDρ, _, hb⟩ := quarticDensity_gradient_source f hf h4 hd M L hM hL hfb hdb
  have hbρ : ∀ᵐ y : Space, ‖quarticDensity f y‖ ≤ M ^ 4 := by
    filter_upwards [hfb] with y hy
    simpa only [quarticDensity, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)] using
      pow_le_pow_left₀ (norm_nonneg _) hy 4
  exact potential_hasFDerivAt_of_core_approximation (quarticDensity f)
    (fderiv ℝ (quarticDensity f)) ρn hc hn hρ hDρ
    (M ^ 4) (4 * M ^ 3 * L) (by positivity) (by positivity) hbρ hb
    ε hε hεlim he0 he1 hi0 hi1

end HBL.RegularRadiation.QuarticGradient
