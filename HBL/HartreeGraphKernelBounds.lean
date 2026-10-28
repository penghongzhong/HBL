import HBL.HartreeSpatialCompletion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
Concrete inverse-square convolution estimates for the physical graph source class.
The density estimate uses L-infinity and L^(3/2); the gradient estimate uses
L1 and L^(25/8).  Neither estimate assumes an L2 background or a bounded
density gradient.  All near/far kernel integrability is proved below.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology

namespace HBL.RegularRadiation.GraphKernel

/-- The complementary part of the actual inverse-square kernel. -/
def farKernel (x : Space) : ℝ :=
  (ball (0 : Space) 1)ᶜ.indicator kernel x

private theorem kernel_nonneg (x : Space) : 0 ≤ kernel x := by
  exact inv_nonneg.mpr (sq_nonneg _)

private theorem near_nonneg (x : Space) : 0 ≤ nearKernel x :=
  indicator_nonneg (fun y _ => kernel_nonneg y) x

private theorem far_nonneg (x : Space) : 0 ≤ farKernel x :=
  indicator_nonneg (fun y _ => kernel_nonneg y) x

private theorem kernel_measurable : Measurable kernel := by
  unfold kernel
  fun_prop

private theorem near_measurable : Measurable nearKernel :=
  kernel_measurable.indicator measurableSet_ball

private theorem far_measurable : Measurable farKernel :=
  kernel_measurable.indicator measurableSet_ball.compl

private theorem split_kernel (x : Space) :
    kernel x = nearKernel x + farKernel x := by
  by_cases hx : x ∈ ball (0 : Space) 1
  · simp [nearKernel, farKernel, hx]
  · simp [nearKernel, farKernel, hx]

private theorem far_le_one (x : Space) : farKernel x ≤ 1 := by
  by_cases hx : x ∈ ball (0 : Space) 1
  · simp [farKernel, hx]
  · have hn : 1 ≤ ‖x‖ := by simpa only [mem_ball_zero_iff, not_lt] using hx
    have hs : 1 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    simpa [farKernel, hx, kernel] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs)

private theorem near_memLp : MemLp nearKernel (25 / 17 : ℝ≥0∞) := by
  have hp (x : Space) : ‖kernel x‖ ^ (25 / 17 : ℝ) =
      ‖x‖ ^ (-(50 / 17 : ℝ)) := by
    rw [Real.norm_of_nonneg (kernel_nonneg x)]
    have hk : kernel x = ‖x‖ ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (norm_nonneg x), Real.rpow_two]
      rfl
    rw [hk, ← Real.rpow_mul (norm_nonneg x)]
    norm_num
  have hi : IntegrableOn (fun x : Space => ‖kernel x‖ ^ (25 / 17 : ℝ))
      (ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 50 / 17)
      (by norm_num [Space]) (by norm_num [Space])
    · filter_upwards with x
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), hp]
      simp only [one_mul, le_refl]
    · exact (kernel_measurable.norm.pow_const (25 / 17 : ℝ)).aestronglyMeasurable
  have hi' : Integrable (fun x : Space => ‖nearKernel x‖ ^ (25 / 17 : ℝ)) := by
    convert (integrable_indicator_iff measurableSet_ball).mpr hi using 1
    funext x
    by_cases hx : x ∈ ball (0 : Space) 1
    · simp [nearKernel, hx]
    · simp [nearKernel, hx]
  apply (integrable_norm_rpow_iff near_measurable.aestronglyMeasurable
    (by norm_num : (25 / 17 : ℝ≥0∞) ≠ 0) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  simpa using hi'

private theorem far_memLp : MemLp farKernel (3 : ℝ≥0∞) := by
  have hi : Integrable (fun x : Space => ((1 + ‖x‖ ^ 2)⁻¹) ^ 3) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := Space) (μ := volume)
      (r := 6) (by norm_num [Space])
    convert h using 1
    funext x
    norm_num
  have hb (x : Space) : ‖farKernel x‖ ^ 3 ≤
      8 * ((1 + ‖x‖ ^ 2)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg (far_nonneg x)]
    by_cases hx : x ∈ ball (0 : Space) 1
    · simp [farKernel, hx]
      positivity
    · have hn : 1 ≤ ‖x‖ := by simpa only [mem_ball_zero_iff, not_lt] using hx
      have hs : 1 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      have hk : kernel x ≤ 2 * (1 + ‖x‖ ^ 2)⁻¹ := by
        rw [kernel, ← one_div, ← div_eq_mul_inv]
        apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
        nlinarith
      simpa [farKernel, hx, mul_pow, show (2 : ℝ) ^ 3 = 8 by norm_num] using
        pow_le_pow_left₀ (kernel_nonneg x) hk 3
  have hi' : Integrable (fun x : Space => ‖farKernel x‖ ^ 3) := by
    apply (hi.const_mul 8).mono' ((far_measurable.norm.pow_const (3 : ℕ)).aestronglyMeasurable)
    filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity)]
    exact hb x
  apply (integrable_norm_rpow_iff far_measurable.aestronglyMeasurable
    (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
  simpa using hi'

private theorem integral_kernel_holder {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (K : Space → ℝ) (f : Space → E) (hK : MemLp K p) (hf : MemLp f q)
    (x : Space) :
    Integrable (fun y : Space => K (x - y) • f y) ∧
      ‖∫ y : Space, K (x - y) • f y‖ ≤
        lpNorm K p volume * lpNorm f q volume := by
  have hmp := (volume : Measure Space).measurePreserving_sub_left x
  have hkx : MemLp (fun y : Space => K (x - y)) p := hK.comp_measurePreserving hmp
  have hi : MemLp (fun y : Space => K (x - y) • f y) 1 := hkx.smul hf
  refine ⟨memLp_one_iff_integrable.mp hi, ?_⟩
  have hh := eLpNorm_smul_le_mul_eLpNorm hkx.aestronglyMeasurable
    hf.aestronglyMeasurable (p := p) (q := q) (r := 1)
  have hhr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hkx.eLpNorm_ne_top hf.eLpNorm_ne_top) hh
  have hkn : eLpNorm (fun y : Space => K (x - y)) p volume = eLpNorm K p volume :=
    eLpNorm_comp_measurePreserving hK.aestronglyMeasurable hmp
  rw [ENNReal.toReal_mul, hkn] at hhr
  calc
    ‖∫ y : Space, K (x - y) • f y‖ ≤ ∫ y : Space, ‖K (x - y) • f y‖ :=
      norm_integral_le_integral_norm _
    _ = lpNorm (fun y : Space => K (x - y) • f y) 1 volume :=
      (lpNorm_one_eq_integral_norm hi.aestronglyMeasurable).symm
    _ ≤ lpNorm K p volume * lpNorm f q volume := hhr

private theorem kernel_split_integral_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Space → E) (x : Space) (A B : ℝ)
    (hn : Integrable (fun y : Space => nearKernel (x - y) • f y))
    (hf : Integrable (fun y : Space => farKernel (x - y) • f y))
    (hnb : ‖∫ y : Space, nearKernel (x - y) • f y‖ ≤ A)
    (hfb : ‖∫ y : Space, farKernel (x - y) • f y‖ ≤ B) :
    Integrable (fun y : Space => kernel (x - y) • f y) ∧
      ‖∫ y : Space, kernel (x - y) • f y‖ ≤ A + B := by
  have heq : (fun y : Space => kernel (x - y) • f y) =
      fun y => nearKernel (x - y) • f y + farKernel (x - y) • f y := by
    funext y
    rw [split_kernel, add_smul]
  rw [heq]
  refine ⟨hn.add hf, ?_⟩
  rw [integral_add hn hf]
  exact (norm_add_le _ _).trans (add_le_add hnb hfb)

/-- Uniform bound for the actual complex potential with the graph-space
density assumptions L-infinity and L^(3/2). -/
theorem potential_graph_bound (ρ : Space → ℂ)
    (hρtop : MemLp ρ ∞) (hρ : MemLp ρ (3 / 2 : ℝ≥0∞)) (x : Space) :
    Integrable (fun y : Space => (kernel (x - y) : ℂ) * ρ y) ∧
      ‖potential ρ x‖ ≤ nearMass * lpNorm ρ ∞ volume +
        lpNorm farKernel 3 volume * lpNorm ρ (3 / 2) volume := by
  let : ENNReal.HolderConjugate (3 : ℝ≥0∞) (3 / 2 : ℝ≥0∞) :=
    ⟨by
      norm_num only [inv_one]
      rw [ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      rw [div_eq_mul_inv]
      calc
        _ = (3 : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ := by ring
        _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)⟩
  have hn := integral_kernel_holder nearKernel ρ
    (memLp_one_iff_integrable.mpr regularRadiationKernel_checks.1) hρtop x
  have hf := integral_kernel_holder farKernel ρ far_memLp hρ x
  have hmass : lpNorm nearKernel 1 volume = nearMass := by
    rw [lpNorm_one_eq_integral_norm near_measurable.aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => Real.norm_of_nonneg (near_nonneg y))
  rw [hmass] at hn
  simpa only [potential, Complex.real_smul] using
    kernel_split_integral_bound ρ x _ _ hn.1 hf.1 hn.2 hf.2

/-- Uniform bound for the actual operator-valued gradient potential with
L1 and L^(25/8) gradient data. -/
theorem gradientPotential_graph_bound (D : Space → Space →L[ℝ] ℂ)
    (hD : Integrable D) (hDp : MemLp D (25 / 8 : ℝ≥0∞)) (x : Space) :
    Integrable (fun y : Space => (kernel (x - y) : ℂ) • D y) ∧
      ‖SpatialCompletion.gradientPotential D x‖ ≤
        lpNorm nearKernel (25 / 17) volume * lpNorm D (25 / 8) volume +
          ∫ y : Space, ‖D y‖ := by
  let : ENNReal.HolderConjugate (25 / 17 : ℝ≥0∞) (25 / 8 : ℝ≥0∞) :=
    ⟨by
      norm_num only [inv_one]
      rw [ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)),
        ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num [div_eq_mul_inv, ← add_mul, ENNReal.mul_inv_cancel]⟩
  have hn := integral_kernel_holder nearKernel D near_memLp hDp x
  have hfar : MemLp farKernel ∞ := memLp_top_of_bound
    far_measurable.aestronglyMeasurable 1 <| Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (far_nonneg y)]
      exact far_le_one y
  have hf := integral_kernel_holder farKernel D hfar (memLp_one_iff_integrable.mpr hD) x
  have hfn : lpNorm farKernel ∞ volume ≤ 1 := by
    have h := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure Space)) (C := (1 : ℝ))
      (Eventually.of_forall fun y => (Real.norm_of_nonneg (far_nonneg y)).le.trans
        (far_le_one y))
    rw [← eLpNorm_exponent_top far_measurable.aestronglyMeasurable] at h
    have hh := ENNReal.toReal_mono (by simp : ENNReal.ofReal (1 : ℝ) ≠ ∞) h
    simpa [lpNorm] using hh
  have hfb : ‖∫ y : Space, farKernel (x - y) • D y‖ ≤ ∫ y : Space, ‖D y‖ := by
    calc
      _ ≤ lpNorm farKernel ∞ volume * lpNorm D 1 volume := hf.2
      _ ≤ 1 * lpNorm D 1 volume := mul_le_mul_of_nonneg_right hfn lpNorm_nonneg
      _ = ∫ y : Space, ‖D y‖ := by
        rw [one_mul, lpNorm_one_eq_integral_norm hD.aestronglyMeasurable]
  have heq : (fun y : Space => (kernel (x - y) : ℂ) • D y) =
      fun y : Space => kernel (x - y) • D y := by
    funext y
    ext v
    simp only [smul_apply, Complex.real_smul, smul_eq_mul]
  unfold SpatialCompletion.gradientPotential
  rw [heq]
  exact kernel_split_integral_bound D x _ _ hn.1 hf.1 hn.2 hfb

end HBL.RegularRadiation.GraphKernel
