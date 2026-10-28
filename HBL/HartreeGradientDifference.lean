import HBL.HartreeFirstOrderSource

/-!
# First-order differences of the actual quartic Hartree potential

Both the field increment and its spatial differential are retained. The
potential difference and its actual differential are bounded linearly in
those increments. Neither field is required to be in L2 or to have compact
support. No approximation sequence, convolution derivative, or potential
Lipschitz bound is assumed. This is a source estimate, not an existence
statement for the constrained evolution or the manuscript main theorem.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Topology
namespace HBL.RegularRadiation.GradientDifference
open SpatialCompletion QuarticGradient LocalCutoff

private theorem norm_square_difference (a b : ℂ) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  rw [show ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]
  exact (mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le a b)
    (add_nonneg (norm_nonneg a) (norm_nonneg b))).trans_eq (by ring)

/-- The spatial density difference retains the cubic field factor and the
quadratic coefficients needed for integration without a background L2 norm. -/
theorem quarticDensity_fderiv_difference (f g : Space → ℂ) {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (quarticDensity f) x - fderiv ℝ (quarticDensity g) x‖ ≤
      4 * ‖f x‖ ^ 3 * ‖fderiv ℝ f x - fderiv ℝ g x‖ +
      8 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) * ‖f x - g x‖ * ‖fderiv ℝ g x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖fderiv ℝ (quarticDensity f) x v - fderiv ℝ (quarticDensity g) x v‖ ≤ _
  rw [quarticDensity_fderiv_apply f hf, quarticDensity_fderiv_apply g hg,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have he : 4 * ‖f x‖ ^ 2 * inner ℝ (f x) (fderiv ℝ f x v) -
      4 * ‖g x‖ ^ 2 * inner ℝ (g x) (fderiv ℝ g x v) =
      4 * (‖f x‖ ^ 2 * inner ℝ (f x) ((fderiv ℝ f x - fderiv ℝ g x) v) +
        ‖f x‖ ^ 2 * inner ℝ (f x - g x) (fderiv ℝ g x v) +
        (‖f x‖ ^ 2 - ‖g x‖ ^ 2) * inner ℝ (g x) (fderiv ℝ g x v)) := by
    change 4 * ‖f x‖ ^ 2 * inner ℝ (f x) (fderiv ℝ f x v) -
      4 * ‖g x‖ ^ 2 * inner ℝ (g x) (fderiv ℝ g x v) =
      4 * (‖f x‖ ^ 2 * inner ℝ (f x) (fderiv ℝ f x v - fderiv ℝ g x v) +
        ‖f x‖ ^ 2 * inner ℝ (f x - g x) (fderiv ℝ g x v) +
        (‖f x‖ ^ 2 - ‖g x‖ ^ 2) * inner ℝ (g x) (fderiv ℝ g x v))
    rw [inner_sub_right, inner_sub_left]
    ring
  have hip (a b : ℂ) : |inner ℝ a b| ≤ ‖a‖ * ‖b‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) a b
  have h1 : |‖f x‖ ^ 2 * inner ℝ (f x) ((fderiv ℝ f x - fderiv ℝ g x) v)| ≤
      ‖f x‖ ^ 3 * ‖fderiv ℝ f x - fderiv ℝ g x‖ * ‖v‖ := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ‖f x‖ ^ 2 * (‖f x‖ * (‖fderiv ℝ f x - fderiv ℝ g x‖ * ‖v‖)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact (hip _ _).trans (mul_le_mul_of_nonneg_left
          ((fderiv ℝ f x - fderiv ℝ g x).le_opNorm v) (norm_nonneg _))
      _ = _ := by ring
  have h2 : |‖f x‖ ^ 2 * inner ℝ (f x - g x) (fderiv ℝ g x v)| ≤
      ‖f x‖ ^ 2 * ‖f x - g x‖ * ‖fderiv ℝ g x‖ * ‖v‖ := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ‖f x‖ ^ 2 * (‖f x - g x‖ * (‖fderiv ℝ g x‖ * ‖v‖)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact (hip _ _).trans (mul_le_mul_of_nonneg_left
          ((fderiv ℝ g x).le_opNorm v) (norm_nonneg _))
      _ = _ := by ring
  have h3 : |(‖f x‖ ^ 2 - ‖g x‖ ^ 2) * inner ℝ (g x) (fderiv ℝ g x v)| ≤
      (‖f x‖ + ‖g x‖) * ‖f x - g x‖ * ‖g x‖ * ‖fderiv ℝ g x‖ * ‖v‖ := by
    rw [abs_mul]
    have ht := mul_le_mul (norm_square_difference (f x) (g x))
      ((hip _ _).trans (mul_le_mul_of_nonneg_left
        ((fderiv ℝ g x).le_opNorm v) (norm_nonneg _))) (abs_nonneg _) (by positivity)
    exact ht.trans_eq (by ring)
  have hcoeff : ‖f x‖ ^ 2 + (‖f x‖ + ‖g x‖) * ‖g x‖ ≤
      2 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) := by
    nlinarith only [sq_nonneg (‖f x‖ - ‖g x‖), sq_nonneg ‖f x‖, sq_nonneg ‖g x‖]
  rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4 * ((|‖f x‖ ^ 2 * inner ℝ (f x) ((fderiv ℝ f x - fderiv ℝ g x) v)| +
        |‖f x‖ ^ 2 * inner ℝ (f x - g x) (fderiv ℝ g x v)|) +
        |(‖f x‖ ^ 2 - ‖g x‖ ^ 2) * inner ℝ (g x) (fderiv ℝ g x v)|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 4 * ((‖f x‖ ^ 3 * ‖fderiv ℝ f x - fderiv ℝ g x‖ * ‖v‖ +
        ‖f x‖ ^ 2 * ‖f x - g x‖ * ‖fderiv ℝ g x‖ * ‖v‖) +
        (‖f x‖ + ‖g x‖) * ‖f x - g x‖ * ‖g x‖ * ‖fderiv ℝ g x‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) (by norm_num)
    _ = 4 * (‖f x‖ ^ 3 * ‖fderiv ℝ f x - fderiv ℝ g x‖ +
        (‖f x‖ ^ 2 + (‖f x‖ + ‖g x‖) * ‖g x‖) *
          ‖f x - g x‖ * ‖fderiv ℝ g x‖) * ‖v‖ := by ring
    _ ≤ 4 * (‖f x‖ ^ 3 * ‖fderiv ℝ f x - fderiv ℝ g x‖ +
        (2 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2)) * ‖f x - g x‖ * ‖fderiv ℝ g x‖) * ‖v‖ := by
      gcongr
    _ = _ := by ring

private theorem quartic_difference_refined (a b : ℂ) {M : ℝ}
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    |‖a‖ ^ 4 - ‖b‖ ^ 4| ≤ 2 * M * (‖a‖ ^ 2 + ‖b‖ ^ 2) * ‖a - b‖ := by
  rw [show ‖a‖ ^ 4 - ‖b‖ ^ 4 = (‖a‖ ^ 2 - ‖b‖ ^ 2) *
    (‖a‖ ^ 2 + ‖b‖ ^ 2) by ring, abs_mul,
    abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  calc
    _ ≤ ((‖a‖ + ‖b‖) * ‖a - b‖) * (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (norm_square_difference a b) (by positivity)
    _ ≤ ((2 * M) * ‖a - b‖) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
      gcongr
      linarith
    _ = _ := by ring

private theorem mixed_product_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : Space → E) (g : Space → F) (hf : MemLp f 2) (hg : MemLp g 2)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hfa : (∫ x : Space, ‖f x‖ ^ 2) ≤ a ^ 2)
    (hgb : (∫ x : Space, ‖g x‖ ^ 2) ≤ b ^ 2) :
    Integrable (fun x : Space => ‖f x‖ * ‖g x‖) ∧
    (∫ x : Space, ‖f x‖ * ‖g x‖) ≤ 2 * a * b := by
  have hp (x : Space) : ‖f x‖ * ‖g x‖ ≤
      (b / a) * ‖f x‖ ^ 2 + (a / b) * ‖g x‖ ^ 2 := by
    have he : (b / a) * ‖f x‖ ^ 2 + (a / b) * ‖g x‖ ^ 2 =
        (b ^ 2 * ‖f x‖ ^ 2 + a ^ 2 * ‖g x‖ ^ 2) / (a * b) := by field_simp
    rw [he]
    apply (le_div_iff₀ (mul_pos ha hb)).2
    nlinarith only [sq_nonneg (b * ‖f x‖ - a * ‖g x‖),
      mul_nonneg (mul_nonneg ha.le hb.le) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hmaj := (hf.norm.integrable_sq.const_mul (b / a)).add
    (hg.norm.integrable_sq.const_mul (a / b))
  have hi : Integrable (fun x : Space => ‖f x‖ * ‖g x‖) := by
    apply hmaj.mono' (hf.aestronglyMeasurable.norm.mul hg.aestronglyMeasurable.norm)
    filter_upwards with x
    simpa only [Pi.add_apply, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hp x
  refine ⟨hi, ?_⟩
  have ht := integral_mono_ae hi hmaj (Filter.Eventually.of_forall hp)
  simp only [Pi.add_apply] at ht
  rw [integral_add (hf.norm.integrable_sq.const_mul (b / a))
    (hg.norm.integrable_sq.const_mul (a / b)), integral_const_mul, integral_const_mul] at ht
  calc
    _ ≤ (b / a) * (∫ x : Space, ‖f x‖ ^ 2) + (a / b) * (∫ x : Space, ‖g x‖ ^ 2) := ht
    _ ≤ (b / a) * a ^ 2 + (a / b) * b ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hfa (by positivity))
        (mul_le_mul_of_nonneg_left hgb (by positivity))
    _ = _ := by field_simp; ring

private theorem field_powers (f : Space → ℂ) (hf : Continuous f)
    (h4 : Integrable (fun x : Space => ‖f x‖ ^ 4))
    {M j : ℝ} (hM : 0 ≤ M) (hj : 0 < j)
    (hb : ∀ᵐ x, ‖f x‖ ≤ M) (hJ : (∫ x : Space, ‖f x‖ ^ 4) ≤ j ^ 2) :
    MemLp (fun x : Space => ‖f x‖ ^ 2) 2 ∧
    (∫ x : Space, ‖‖f x‖ ^ 2‖ ^ 2) ≤ j ^ 2 ∧
    MemLp (fun x : Space => ‖f x‖ ^ 3) 2 ∧
    (∫ x : Space, ‖‖f x‖ ^ 3‖ ^ 2) ≤ ((M + 1) * j) ^ 2 := by
  have he4 : (fun x : Space => ‖‖f x‖ ^ 2‖ ^ 2) = fun x => ‖f x‖ ^ 4 := by
    funext x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    ring
  have he6 : (fun x : Space => ‖‖f x‖ ^ 3‖ ^ 2) = fun x => ‖f x‖ ^ 6 := by
    funext x
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 3)]
    ring
  have hdom : ∀ᵐ x, ‖f x‖ ^ 6 ≤ M ^ 2 * ‖f x‖ ^ 4 := by
    filter_upwards [hb] with x hx
    calc
      _ = ‖f x‖ ^ 2 * ‖f x‖ ^ 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hx 2) (by positivity)
  have h6 : Integrable (fun x : Space => ‖f x‖ ^ 6) := by
    apply (h4.const_mul (M ^ 2)).mono' (hf.aestronglyMeasurable.norm.pow 6)
    filter_upwards [hdom] with x hx
    simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 6)] using hx
  refine ⟨(memLp_two_iff_integrable_sq_norm (hf.aestronglyMeasurable.norm.pow 2)).2
    (by rw [he4]; exact h4), by rw [he4]; exact hJ,
    (memLp_two_iff_integrable_sq_norm (hf.aestronglyMeasurable.norm.pow 3)).2
    (by rw [he6]; exact h6), ?_⟩
  rw [he6]
  have ht := integral_mono_ae h6 (h4.const_mul (M ^ 2)) hdom
  rw [integral_const_mul] at ht
  calc
    _ ≤ M ^ 2 * (∫ x : Space, ‖f x‖ ^ 4) := ht
    _ ≤ M ^ 2 * j ^ 2 := mul_le_mul_of_nonneg_left hJ (sq_nonneg _)
    _ ≤ ((M + 1) * j) ^ 2 := by rw [mul_pow]; gcongr; linarith

/-- Actual potential and actual potential differential obey simultaneous
Lipschitz estimates. All nonlocal integrability and derivative-identification
obligations are discharged from the displayed field hypotheses. -/
theorem quartic_potential_first_order_difference
    (f g : Space → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hf4 : Integrable (fun x : Space => ‖f x‖ ^ 4))
    (hg4 : Integrable (fun x : Space => ‖g x‖ ^ 4))
    (hDf : MemLp (fderiv ℝ f) 2) (hDg : MemLp (fderiv ℝ g) 2)
    (hfg : MemLp (fun x => f x - g x) 2)
    {M L j Q d : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hj : 0 < j) (hQ : 0 < Q) (hd : 0 < d)
    (hfb : ∀ᵐ x, ‖f x‖ ≤ M) (hgb : ∀ᵐ x, ‖g x‖ ≤ M)
    (hDfb : ∀ᵐ x, ‖fderiv ℝ f x‖ ≤ L) (hDgb : ∀ᵐ x, ‖fderiv ℝ g x‖ ≤ L)
    (hJf : (∫ x : Space, ‖f x‖ ^ 4) ≤ j ^ 2)
    (hJg : (∫ x : Space, ‖g x‖ ^ 4) ≤ j ^ 2)
    (hEg : (∫ x : Space, ‖fderiv ℝ g x‖ ^ 2) ≤ Q ^ 2)
    (hδ : ∀ᵐ x, ‖f x - g x‖ ≤ d)
    (hDδ : ∀ᵐ x, ‖fderiv ℝ f x - fderiv ℝ g x‖ ≤ d)
    (hδ2 : (∫ x : Space, ‖f x - g x‖ ^ 2) ≤ d ^ 2)
    (hDδ2 : (∫ x : Space, ‖fderiv ℝ f x - fderiv ℝ g x‖ ^ 2) ≤ d ^ 2) :
    ∀ x : Space,
      ‖potential (quarticDensity f) x - potential (quarticDensity g) x‖ ≤
        (4 * nearMass * M ^ 3 + 8 * M * j) * d ∧
      ‖fderiv ℝ (potential (quarticDensity f)) x -
        fderiv ℝ (potential (quarticDensity g)) x‖ ≤
        (nearMass * (4 * M ^ 3 + 16 * M ^ 2 * L) +
          8 * (M + 1) * j + 32 * j * Q) * d := by
  obtain ⟨hiF, hiDF, _, hbDF⟩ := quarticDensity_gradient_source f hf hf4 hDf M L hM hL hfb hDfb
  obtain ⟨hiG, hiDG, _, hbDG⟩ := quarticDensity_gradient_source g hg hg4 hDg M L hM hL hgb hDgb
  obtain ⟨hf2, hf2I, hf3, hf3I⟩ := field_powers f hf.continuous hf4 hM hj hfb hJf
  obtain ⟨hg2, hg2I, _, _⟩ := field_powers g hg.continuous hg4 hM hj hgb hJg
  have pf := mixed_product_bound (fun x => ‖f x‖ ^ 2) (fun x => f x - g x)
    hf2 hfg hj hd hf2I hδ2
  have pg := mixed_product_bound (fun x => ‖g x‖ ^ 2) (fun x => f x - g x)
    hg2 hfg hj hd hg2I hδ2
  have pd := mixed_product_bound (fun x => ‖f x‖ ^ 3)
    (fun x => fderiv ℝ f x - fderiv ℝ g x) hf3 (hDf.sub hDg)
    (mul_pos (by linarith) hj) hd hf3I hDδ2
  have qf := mixed_product_bound (fun x => ‖f x‖ ^ 2) (fderiv ℝ g)
    hf2 hDg hj hQ hf2I hEg
  have qg := mixed_product_bound (fun x => ‖g x‖ ^ 2) (fderiv ℝ g)
    hg2 hDg hj hQ hg2I hEg
  simp only [Real.norm_of_nonneg (sq_nonneg _)] at pf pg qf qg
  simp only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 3)] at pd
  have hv : ∀ᵐ x, ‖quarticDensity f x - quarticDensity g x‖ ≤
      2 * M * (‖f x‖ ^ 2 * ‖f x - g x‖ + ‖g x‖ ^ 2 * ‖f x - g x‖) := by
    filter_upwards [hfb, hgb] with x hfx hgx
    have ht := quartic_difference_refined (f x) (g x) hfx hgx
    simpa only [quarticDensity, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      mul_add, mul_assoc] using ht
  have hIv : (∫ x : Space, ‖quarticDensity f x - quarticDensity g x‖) ≤ 8 * M * j * d := by
    have ht := integral_mono_ae (hiF.sub hiG).norm ((pf.1.add pg.1).const_mul (2 * M)) hv
    simp only [Pi.add_apply] at ht
    rw [integral_const_mul, integral_add pf.1 pg.1] at ht
    calc
      _ ≤ 2 * M * ((∫ x : Space, ‖f x‖ ^ 2 * ‖f x - g x‖) +
          ∫ x : Space, ‖g x‖ ^ 2 * ‖f x - g x‖) := ht
      _ ≤ 2 * M * (2 * j * d + 2 * j * d) :=
        mul_le_mul_of_nonneg_left (add_le_add pf.2 pg.2) (by positivity)
      _ = _ := by ring
  have hdpt : ∀ᵐ x, ‖fderiv ℝ (quarticDensity f) x - fderiv ℝ (quarticDensity g) x‖ ≤
      4 * (‖f x‖ ^ 3 * ‖fderiv ℝ f x - fderiv ℝ g x‖) +
        8 * d * (‖f x‖ ^ 2 * ‖fderiv ℝ g x‖ + ‖g x‖ ^ 2 * ‖fderiv ℝ g x‖) := by
    filter_upwards [hδ] with x hx
    calc
      _ ≤ 4 * ‖f x‖ ^ 3 * ‖fderiv ℝ f x - fderiv ℝ g x‖ +
        8 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) * ‖f x - g x‖ * ‖fderiv ℝ g x‖ :=
        quarticDensity_fderiv_difference f g (hf.differentiable (by norm_num) x)
          (hg.differentiable (by norm_num) x)
      _ ≤ 4 * ‖f x‖ ^ 3 * ‖fderiv ℝ f x - fderiv ℝ g x‖ +
        8 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) * d * ‖fderiv ℝ g x‖ := by gcongr
      _ = _ := by ring
  have hId : (∫ x : Space, ‖fderiv ℝ (quarticDensity f) x - fderiv ℝ (quarticDensity g) x‖) ≤
      (8 * (M + 1) * j + 32 * j * Q) * d := by
    have ht := integral_mono_ae (hiDF.sub hiDG).norm
      ((pd.1.const_mul 4).add ((qf.1.add qg.1).const_mul (8 * d))) hdpt
    simp only [Pi.add_apply] at ht
    rw [integral_add (pd.1.const_mul 4) ((qf.1.add qg.1).const_mul (8 * d)),
      integral_const_mul, integral_const_mul, integral_add qf.1 qg.1] at ht
    calc
      _ ≤ 4 * (∫ x : Space, ‖f x‖ ^ 3 * ‖fderiv ℝ f x - fderiv ℝ g x‖) +
          8 * d * ((∫ x : Space, ‖f x‖ ^ 2 * ‖fderiv ℝ g x‖) +
            ∫ x : Space, ‖g x‖ ^ 2 * ‖fderiv ℝ g x‖) := ht
      _ ≤ 4 * (2 * ((M + 1) * j) * d) + 8 * d * (2 * j * Q + 2 * j * Q) :=
        add_le_add (mul_le_mul_of_nonneg_left pd.2 (by norm_num))
          (mul_le_mul_of_nonneg_left (add_le_add qf.2 qg.2) (by positivity))
      _ = _ := by ring
  have hbρ (u : Space → ℂ) (hu : ∀ᵐ x, ‖u x‖ ≤ M) :
      ∀ᵐ x, ‖quarticDensity u x‖ ≤ M ^ 4 := by
    filter_upwards [hu] with x hx
    simpa only [quarticDensity, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)] using pow_le_pow_left₀ (norm_nonneg _) hx 4
  have hbdρ : ∀ᵐ x, ‖quarticDensity f x - quarticDensity g x‖ ≤ 4 * M ^ 3 * d := by
    filter_upwards [hfb, hgb, hδ] with x hx hy hz
    have ht := quartic_difference_refined (f x) (g x) hx hy
    have hs : ‖f x‖ ^ 2 + ‖g x‖ ^ 2 ≤ 2 * M ^ 2 := by
      nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hx 2, pow_le_pow_left₀ (norm_nonneg _) hy 2]
    change ‖((‖f x‖ ^ 4 : ℝ) : ℂ) - ((‖g x‖ ^ 4 : ℝ) : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact ht.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hz
      (norm_nonneg _) (by positivity)).trans_eq (by ring))
  have hbDρ : ∀ᵐ x, ‖fderiv ℝ (quarticDensity f) x - fderiv ℝ (quarticDensity g) x‖ ≤
      (4 * M ^ 3 + 16 * M ^ 2 * L) * d := by
    filter_upwards [hfb, hgb, hDgb, hδ, hDδ] with x hx hy hdy hz hdz
    have ht := quarticDensity_fderiv_difference f g (hf.differentiable (by norm_num) x)
      (hg.differentiable (by norm_num) x)
    calc
      _ ≤ 4 * ‖f x‖ ^ 3 * ‖fderiv ℝ f x - fderiv ℝ g x‖ +
          8 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) * ‖f x - g x‖ * ‖fderiv ℝ g x‖ := ht
      _ ≤ 4 * M ^ 3 * d + 8 * (M ^ 2 + M ^ 2) * d * L := by gcongr
      _ = _ := by ring
  intro x
  constructor
  · have ht := potential_sub_bound (quarticDensity f) (quarticDensity g) hiF hiG
      (M ^ 4) (M ^ 4) (4 * M ^ 3 * d) (by positivity) (by positivity) (by positivity)
      (hbρ f hfb) (hbρ g hgb) hbdρ x
    exact (ht.trans (add_le_add le_rfl hIv)).trans_eq (by ring)
  · rw [(quarticPotential_hasFDerivAt_noncompact f hf hf4 hDf M L hM hL hfb hDfb x).fderiv,
        (quarticPotential_hasFDerivAt_noncompact g hg hg4 hDg M L hM hL hgb hDgb x).fderiv]
    have ht := gradientPotential_difference_bound (fderiv ℝ (quarticDensity f))
      (fderiv ℝ (quarticDensity g)) hiDF hiDG (4 * M ^ 3 * L) (4 * M ^ 3 * L)
      ((4 * M ^ 3 + 16 * M ^ 2 * L) * d) (by positivity) (by positivity) (by positivity)
      hbDF hbDG hbDρ x
    exact (ht.trans (add_le_add le_rfl hId)).trans_eq (by ring)

#print axioms quarticDensity_fderiv_difference
#print axioms quartic_potential_first_order_difference
end HBL.RegularRadiation.GradientDifference
