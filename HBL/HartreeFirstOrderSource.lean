import HBL.HartreeLocalCutoff
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Complete first-order sources for the physical seventh-order Hartree expression

Prove the noncompact derivative formula, L2 bounds for the entire nonlinearity
and its entire differential, and the weak-derivative integration identity.
Both differentiated factors are retained. The input field needs L4, not L2;
no support or approximation premise is introduced. Identification with the
higher Bessel-potential scale, differentiated Taylor-remainder difference
bounds, and the constrained evolution remain separate tasks.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Topology

namespace HBL.RegularRadiation.FirstOrderSource

open SpatialCompletion QuarticGradient LocalCutoff

private def cubic (f : Space → ℂ) (x : Space) : ℂ :=
  ((‖f x‖ ^ 2 : ℝ) : ℂ) * f x

private theorem cubic_contDiff (f : Space → ℂ) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (cubic f) :=
  (Complex.ofRealCLM.contDiff.comp (hf.norm_sq ℂ)).mul hf

private theorem cubic_norm (f : Space → ℂ) (x : Space) :
    ‖cubic f x‖ = ‖f x‖ ^ 3 := by
  simp only [cubic, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖f x‖)]
  ring

private theorem cubic_derivative (f : Space → ℂ) {x : Space}
    (hf : DifferentiableAt ℝ f x) (v : Space) :
    fderiv ℝ (cubic f) x v =
      ((‖f x‖ ^ 2 : ℝ) : ℂ) * fderiv ℝ f x v +
        ((2 * inner ℝ (f x) (fderiv ℝ f x v) : ℝ) : ℂ) * f x := by
  have hdq := Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt.norm_sq
  have hd := hdq.mul hf.hasFDerivAt
  have he : fderiv ℝ (cubic f) x =
      ((‖f x‖ ^ 2 : ℝ) : ℂ) • fderiv ℝ f x +
        f x • (Complex.ofRealCLM.comp
          (2 • (innerSL ℝ (f x)).comp (fderiv ℝ f x))) := hd.fderiv
  rw [he]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, Complex.ofRealCLM_apply, innerSL_apply_apply]
  ring

private theorem cubic_derivative_norm (f : Space → ℂ) {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (cubic f) x‖ ≤ 3 * ‖f x‖ ^ 2 * ‖fderiv ℝ f x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hip : |inner ℝ (f x) (fderiv ℝ f x v)| ≤
      ‖f x‖ * ‖fderiv ℝ f x v‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_inner_le_norm (𝕜 := ℝ) (f x) (fderiv ℝ f x v)
  rw [cubic_derivative f hf v]
  calc
    _ ≤ ‖((‖f x‖ ^ 2 : ℝ) : ℂ) * fderiv ℝ f x v‖ +
        ‖((2 * inner ℝ (f x) (fderiv ℝ f x v) : ℝ) : ℂ) * f x‖ := norm_add_le _ _
    _ = ‖f x‖ ^ 2 * ‖fderiv ℝ f x v‖ +
        (2 * |inner ℝ (f x) (fderiv ℝ f x v)|) * ‖f x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg ‖f x‖), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ ‖f x‖ ^ 2 * ‖fderiv ℝ f x v‖ +
        (2 * (‖f x‖ * ‖fderiv ℝ f x v‖)) * ‖f x‖ := by
      gcongr
    _ = (3 * ‖f x‖ ^ 2) * ‖fderiv ℝ f x v‖ := by ring
    _ ≤ (3 * ‖f x‖ ^ 2) * (‖fderiv ℝ f x‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ f x).le_opNorm v) (by positivity)
    _ = (3 * ‖f x‖ ^ 2 * ‖fderiv ℝ f x‖) * ‖v‖ := by ring

/-- The whole physical nonlinearity is differentiable without compact support.
The derivative contains both the differentiated density potential and the
full local cubic derivative; no convolution derivative is supplied as input. -/
theorem hartree_differential_noncompact
    (κ : ℝ) (f : Space → ℂ) (hf : ContDiff ℝ 1 f)
    (h4 : Integrable (fun y : Space => ‖f y‖ ^ 4))
    (hd : MemLp (fderiv ℝ f) 2)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hfb : ∀ᵐ y : Space, ‖f y‖ ≤ M)
    (hdb : ∀ᵐ y : Space, ‖fderiv ℝ f y‖ ≤ L) :
    Differentiable ℝ (hartreeNonlinearity κ f) ∧
    ∀ x v : Space,
      fderiv ℝ (hartreeNonlinearity κ f) x v = (κ : ℂ) *
        (gradientPotential (fderiv ℝ (quarticDensity f)) x v *
            (((‖f x‖ ^ 2 : ℝ) : ℂ) * f x) +
          potential (quarticDensity f) x *
            (((‖f x‖ ^ 2 : ℝ) : ℂ) * fderiv ℝ f x v +
              ((2 * inner ℝ (f x) (fderiv ℝ f x v) : ℝ) : ℂ) * f x)) := by
  have hc := cubic_contDiff f hf
  have hN (x : Space) :=
    ((quarticPotential_hasFDerivAt_noncompact f hf h4 hd M L hM hL hfb hdb x).const_mul
      (κ : ℂ)).mul ((hc.differentiable (by norm_num) x).hasFDerivAt)
  refine ⟨fun x => (hN x).differentiableAt, ?_⟩
  intro x v
  have he : fderiv ℝ (hartreeNonlinearity κ f) x =
      ((κ : ℂ) * potential (quarticDensity f) x) • fderiv ℝ (cubic f) x +
        cubic f x • ((κ : ℂ) • gradientPotential (fderiv ℝ (quarticDensity f)) x) :=
    (hN x).fderiv
  rw [he]
  change ((κ : ℂ) * potential (quarticDensity f) x) * fderiv ℝ (cubic f) x v +
    cubic f x * ((κ : ℂ) * gradientPotential (fderiv ℝ (quarticDensity f)) x v) = _
  rw [cubic_derivative f (hf.differentiable (by norm_num) x) v]
  unfold cubic
  ring

private theorem norm_source_bounds
    (κ : ℝ) (f : Space → ℂ) (hf : ContDiff ℝ 1 f)
    (h4 : Integrable (fun y : Space => ‖f y‖ ^ 4))
    (hd : MemLp (fderiv ℝ f) 2)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hfb : ∀ᵐ y : Space, ‖f y‖ ≤ M)
    (hdb : ∀ᵐ y : Space, ‖fderiv ℝ f y‖ ≤ L) :
    let A := nearMass * M ^ 4 + ∫ y : Space, ‖f y‖ ^ 4
    let B := nearMass * (4 * M ^ 3 * L) +
      2 * (M ^ 2 * (∫ y : Space, ‖f y‖ ^ 4) + ∫ y : Space, ‖fderiv ℝ f y‖ ^ 2)
    ∀ x : Space,
      ‖hartreeNonlinearity κ f x‖ ≤ |κ| * A * ‖f x‖ ^ 3 ∧
      ‖fderiv ℝ (hartreeNonlinearity κ f) x‖ ≤
        |κ| * (B * ‖f x‖ ^ 3 + 3 * A * ‖f x‖ ^ 2 * ‖fderiv ℝ f x‖) := by
  dsimp only
  let A := nearMass * M ^ 4 + ∫ y : Space, ‖f y‖ ^ 4
  let B := nearMass * (4 * M ^ 3 * L) +
    2 * (M ^ 2 * (∫ y : Space, ‖f y‖ ^ 4) + ∫ y : Space, ‖fderiv ℝ f y‖ ^ 2)
  have hA : 0 ≤ A := by
    have hn := regularRadiationKernel_checks.2.1
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    have hn := regularRadiationKernel_checks.2.1
    dsimp [B]
    positivity
  have hρ : Integrable (quarticDensity f) := h4.ofReal
  have hbρ : ∀ᵐ y : Space, ‖quarticDensity f y‖ ≤ M ^ 4 := by
    filter_upwards [hfb] with y hy
    simpa only [quarticDensity, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)] using
      pow_le_pow_left₀ (norm_nonneg _) hy 4
  have hP (x : Space) : ‖potential (quarticDensity f) x‖ ≤ A := by
    have hh := (potential_bound (quarticDensity f) hρ (M ^ 4) (by positivity) hbρ x).2
    simpa only [quarticDensity, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)] using hh
  have hG (x : Space) : ‖gradientPotential (fderiv ℝ (quarticDensity f)) x‖ ≤ B :=
    (quarticDensity_gradient_potential_bound f hf h4 hd M L hM hL hfb hdb x).2
  intro x
  constructor
  · change ‖((κ : ℂ) * potential (quarticDensity f) x) * cubic f x‖ ≤ _
    rw [norm_mul, norm_mul, cubic_norm, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hP x) (abs_nonneg κ)) (by positivity)
  · have hc := cubic_contDiff f hf
    have hNx :=
      ((quarticPotential_hasFDerivAt_noncompact f hf h4 hd M L hM hL hfb hdb x).const_mul
        (κ : ℂ)).mul ((hc.differentiable (by norm_num) x).hasFDerivAt)
    have he : fderiv ℝ (hartreeNonlinearity κ f) x =
        ((κ : ℂ) * potential (quarticDensity f) x) • fderiv ℝ (cubic f) x +
          cubic f x • ((κ : ℂ) • gradientPotential (fderiv ℝ (quarticDensity f)) x) := hNx.fderiv
    rw [he]
    calc
      _ ≤ ‖((κ : ℂ) * potential (quarticDensity f) x) • fderiv ℝ (cubic f) x‖ +
          ‖cubic f x • ((κ : ℂ) • gradientPotential (fderiv ℝ (quarticDensity f)) x)‖ :=
        norm_add_le _ _
      _ = (|κ| * ‖potential (quarticDensity f) x‖) * ‖fderiv ℝ (cubic f) x‖ +
          ‖f x‖ ^ 3 * (|κ| * ‖gradientPotential (fderiv ℝ (quarticDensity f)) x‖) := by
        simp only [norm_smul, norm_mul, cubic_norm, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (|κ| * A) * (3 * ‖f x‖ ^ 2 * ‖fderiv ℝ f x‖) +
          ‖f x‖ ^ 3 * (|κ| * B) := by
        exact add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_left (hP x) (abs_nonneg κ))
            (cubic_derivative_norm f (hf.differentiable (by norm_num) x))
            (norm_nonneg _) (mul_nonneg (abs_nonneg κ) hA))
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hG x) (abs_nonneg κ)) (by positivity))
      _ = |κ| * (B * ‖f x‖ ^ 3 + 3 * A * ‖f x‖ ^ 2 * ‖fderiv ℝ f x‖) := by ring

/-- Entire nonlinearity and entire differential in L2, with explicit squared-norm
bounds. Neither compact support nor L2 membership of the input field is assumed. -/
theorem hartree_first_order_source_noncompact
    (κ : ℝ) (f : Space → ℂ) (hf : ContDiff ℝ 1 f)
    (h4 : Integrable (fun y : Space => ‖f y‖ ^ 4))
    (hd : MemLp (fderiv ℝ f) 2)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hfb : ∀ᵐ y : Space, ‖f y‖ ≤ M)
    (hdb : ∀ᵐ y : Space, ‖fderiv ℝ f y‖ ≤ L) :
    let J := ∫ y : Space, ‖f y‖ ^ 4
    let E := ∫ y : Space, ‖fderiv ℝ f y‖ ^ 2
    let A := nearMass * M ^ 4 + J
    let B := nearMass * (4 * M ^ 3 * L) + 2 * (M ^ 2 * J + E)
    MemLp (hartreeNonlinearity κ f) 2 ∧
    MemLp (fderiv ℝ (hartreeNonlinearity κ f)) 2 ∧
    (∫ y : Space, ‖hartreeNonlinearity κ f y‖ ^ 2) ≤ κ ^ 2 * A ^ 2 * M ^ 2 * J ∧
    (∫ y : Space, ‖fderiv ℝ (hartreeNonlinearity κ f) y‖ ^ 2) ≤
      2 * κ ^ 2 * (B ^ 2 * M ^ 2 * J + 9 * A ^ 2 * M ^ 4 * E) := by
  dsimp only
  let J := ∫ y : Space, ‖f y‖ ^ 4
  let E := ∫ y : Space, ‖fderiv ℝ f y‖ ^ 2
  let A := nearMass * M ^ 4 + J
  let B := nearMass * (4 * M ^ 3 * L) + 2 * (M ^ 2 * J + E)
  have hs := norm_source_bounds κ f hf h4 hd M L hM hL hfb hdb
  have hdiff := (hartree_differential_noncompact κ f hf h4 hd M L hM hL hfb hdb).1
  have hm : AEStronglyMeasurable (hartreeNonlinearity κ f) :=
    hdiff.continuous.aestronglyMeasurable
  have hDm : AEStronglyMeasurable (fderiv ℝ (hartreeNonlinearity κ f)) :=
    (measurable_fderiv (𝕜 := ℝ) (f := hartreeNonlinearity κ f)).aestronglyMeasurable
  have hgd := hd.norm.integrable_sq
  have hv : ∀ᵐ y : Space, ‖hartreeNonlinearity κ f y‖ ^ 2 ≤
      (κ ^ 2 * A ^ 2 * M ^ 2) * ‖f y‖ ^ 4 := by
    filter_upwards [hfb] with y hy
    have h6 : ‖f y‖ ^ 6 ≤ M ^ 2 * ‖f y‖ ^ 4 := by
      calc
        _ = ‖f y‖ ^ 2 * ‖f y‖ ^ 4 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hy 2) (by positivity)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hs y).1 2
    calc
      _ ≤ (|κ| * A * ‖f y‖ ^ 3) ^ 2 := hsq
      _ = (κ ^ 2 * A ^ 2) * ‖f y‖ ^ 6 := by rw [mul_pow, mul_pow, sq_abs]; ring
      _ ≤ (κ ^ 2 * A ^ 2) * (M ^ 2 * ‖f y‖ ^ 4) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = _ := by ring
  have hg : ∀ᵐ y : Space, ‖fderiv ℝ (hartreeNonlinearity κ f) y‖ ^ 2 ≤
      (2 * κ ^ 2) * ((B ^ 2 * M ^ 2) * ‖f y‖ ^ 4 +
        (9 * A ^ 2 * M ^ 4) * ‖fderiv ℝ f y‖ ^ 2) := by
    filter_upwards [hfb] with y hy
    have h6 : ‖f y‖ ^ 6 ≤ M ^ 2 * ‖f y‖ ^ 4 := by
      calc
        _ = ‖f y‖ ^ 2 * ‖f y‖ ^ 4 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hy 2) (by positivity)
    have hfour := pow_le_pow_left₀ (norm_nonneg _) hy 4
    have hb := mul_le_mul_of_nonneg_left h6 (sq_nonneg B)
    have ha := mul_le_mul_of_nonneg_right hfour
      (show 0 ≤ 9 * A ^ 2 * ‖fderiv ℝ f y‖ ^ 2 by positivity)
    have hpoly : (B * ‖f y‖ ^ 3 + 3 * A * ‖f y‖ ^ 2 * ‖fderiv ℝ f y‖) ^ 2 ≤
        2 * ((B ^ 2 * M ^ 2) * ‖f y‖ ^ 4 +
          (9 * A ^ 2 * M ^ 4) * ‖fderiv ℝ f y‖ ^ 2) := by
      nlinarith only [hb, ha,
        sq_nonneg (B * ‖f y‖ ^ 3 - 3 * A * ‖f y‖ ^ 2 * ‖fderiv ℝ f y‖)]
    calc
      _ ≤ (|κ| * (B * ‖f y‖ ^ 3 + 3 * A * ‖f y‖ ^ 2 * ‖fderiv ℝ f y‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hs y).2 2
      _ = κ ^ 2 * (B * ‖f y‖ ^ 3 + 3 * A * ‖f y‖ ^ 2 * ‖fderiv ℝ f y‖) ^ 2 := by
        rw [mul_pow, sq_abs]
      _ ≤ κ ^ 2 * (2 * ((B ^ 2 * M ^ 2) * ‖f y‖ ^ 4 +
          (9 * A ^ 2 * M ^ 4) * ‖fderiv ℝ f y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hpoly (sq_nonneg κ)
      _ = _ := by ring
  have hvmajor := h4.const_mul (κ ^ 2 * A ^ 2 * M ^ 2)
  have hgmajor := ((h4.const_mul (B ^ 2 * M ^ 2)).add
    (hgd.const_mul (9 * A ^ 2 * M ^ 4))).const_mul (2 * κ ^ 2)
  have hvi : Integrable (fun y : Space => ‖hartreeNonlinearity κ f y‖ ^ 2) :=
    hvmajor.mono' (hm.norm.pow 2) (hv.mono fun y hy => by
      simpa only [Real.norm_of_nonneg (sq_nonneg _), Pi.add_apply] using hy)
  have hgi : Integrable (fun y : Space => ‖fderiv ℝ (hartreeNonlinearity κ f) y‖ ^ 2) :=
    hgmajor.mono' (hDm.norm.pow 2) (hg.mono fun y hy => by
      simpa only [Real.norm_of_nonneg (sq_nonneg _), Pi.add_apply] using hy)
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).2 hvi,
    (memLp_two_iff_integrable_sq_norm hDm).2 hgi, ?_, ?_⟩
  · have ht := integral_mono_ae hvi hvmajor hv
    rw [integral_const_mul] at ht
    exact ht
  · have ht := integral_mono_ae hgi hgmajor hg
    simp only [Pi.add_apply] at ht
    rw [integral_const_mul, integral_add (h4.const_mul (B ^ 2 * M ^ 2))
      (hgd.const_mul (9 * A ^ 2 * M ^ 4)), integral_const_mul, integral_const_mul] at ht
    exact ht

/-- The derived L2 differential is genuinely the weak derivative. Every test
product is proved integrable before integration by parts is used. -/
theorem hartree_weak_first_order_source
    (κ : ℝ) (f : Space → ℂ) (hf : ContDiff ℝ 1 f)
    (h4 : Integrable (fun y : Space => ‖f y‖ ^ 4))
    (hd : MemLp (fderiv ℝ f) 2)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hfb : ∀ᵐ y : Space, ‖f y‖ ≤ M)
    (hdb : ∀ᵐ y : Space, ‖fderiv ℝ f y‖ ≤ L) :
    MemLp (hartreeNonlinearity κ f) 2 ∧
    MemLp (fderiv ℝ (hartreeNonlinearity κ f)) 2 ∧
    ∀ φ : Space → ℂ, HasCompactSupport φ → ContDiff ℝ 1 φ → ∀ v : Space,
      Integrable (fun x : Space => hartreeNonlinearity κ f x * fderiv ℝ φ x v) ∧
      Integrable (fun x : Space => fderiv ℝ (hartreeNonlinearity κ f) x v * φ x) ∧
      (∫ x : Space, hartreeNonlinearity κ f x * fderiv ℝ φ x v) =
        -(∫ x : Space, fderiv ℝ (hartreeNonlinearity κ f) x v * φ x) := by
  have hsrc := hartree_first_order_source_noncompact κ f hf h4 hd M L hM hL hfb hdb
  have hdiff := (hartree_differential_noncompact κ f hf h4 hd M L hM hL hfb hdb).1
  refine ⟨hsrc.1, hsrc.2.1, ?_⟩
  intro φ hcφ hφ v
  have ht : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hcφ
  have hDt : MemLp (fderiv ℝ φ) 2 :=
    (hφ.continuous_fderiv (by norm_num)).memLp_of_hasCompactSupport (hcφ.fderiv ℝ)
  have hNv : MemLp (fun x => fderiv ℝ (hartreeNonlinearity κ f) x v) 2 :=
    hsrc.2.1.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ v)
  have htv : MemLp (fun x => fderiv ℝ φ x v) 2 :=
    hDt.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ v)
  have hright := hNv.integrable_mul ht
  have hleft := hsrc.1.integrable_mul htv
  have hbase := hsrc.1.integrable_mul ht
  exact ⟨hleft, hright,
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hright hleft hbase
      (fun x _ => hdiff x) (fun x _ => hφ.differentiable (by norm_num) x)⟩

#print axioms hartree_differential_noncompact
#print axioms hartree_first_order_source_noncompact
#print axioms hartree_weak_first_order_source

end HBL.RegularRadiation.FirstOrderSource
