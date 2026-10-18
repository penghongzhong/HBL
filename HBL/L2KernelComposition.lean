import HBL.L2KernelPointwise

/-!
Composition of two concrete nonnegative Hilbert--Schmidt kernels.

The theorem below is tailored to kernels supported on a full-measure domain
such as the positive half-line.  It proves the operator composition from the
pointwise convolution identity, including all row/column L2 and Fubini
obligations.
-/

noncomputable section

open MeasureTheory

namespace HBL.L2Kernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]

theorem operator_comp_toLp_eq_of_convolution
    (P : α → Prop) (hP : ∀ᵐ x ∂μ, P x)
    (k l m : α → α → ℝ)
    (hk : MemLp (Function.uncurry k) 2 (μ.prod μ))
    (hl : MemLp (Function.uncurry l) 2 (μ.prod μ))
    (hm : MemLp (Function.uncurry m) 2 (μ.prod μ))
    (hk_nonneg : ∀ x y, P x → P y → 0 ≤ k x y)
    (hl_nonneg : ∀ x y, P x → P y → 0 ≤ l x y)
    (hconv : ∀ x y, P x → P y →
      (∫ z, k x z * l z y ∂μ) = m x y) :
    operator (hk.toLp (Function.uncurry k)) ∘L
        operator (hl.toLp (Function.uncurry l)) =
      operator (hm.toLp (Function.uncurry m)) := by
  have hkRow : ∀ᵐ x ∂μ, MemLp (k x) 2 μ := by
    have hmeas := hk.aestronglyMeasurable.prodMk_left
    have hint := hk.integrable_sq.prod_right_ae
    filter_upwards [hmeas, hint] with x hmx hix
    exact (memLp_two_iff_integrable_sq hmx).2 hix
  have hlCol : ∀ᵐ y ∂μ, MemLp (fun x => l x y) 2 μ := by
    have hmeas := hl.aestronglyMeasurable.prodMk_right
    have hint := hl.integrable_sq.prod_left_ae
    filter_upwards [hmeas, hint] with y hmy hiy
    exact (memLp_two_iff_integrable_sq hmy).2 hiy
  have hmRow : ∀ᵐ x ∂μ, MemLp (m x) 2 μ := by
    have hmeas := hm.aestronglyMeasurable.prodMk_left
    have hint := hm.integrable_sq.prod_right_ae
    filter_upwards [hmeas, hint] with x hmx hix
    exact (memLp_two_iff_integrable_sq hmx).2 hix
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext (μ := μ)
  simp only [ContinuousLinearMap.comp_apply]
  have hinner := operator_toLp_ae_eq_integral l hl f
  have houter := operator_toLp_ae_eq_integral k hk
    (operator (hl.toLp (Function.uncurry l)) f)
  have htarget := operator_toLp_ae_eq_integral m hm f
  filter_upwards [hP, hkRow, hmRow, houter, htarget] with x hxP hxk hxm
      hxout hxtarget
  rw [hxout, hxtarget]
  have hdouble : Integrable (Function.uncurry fun s y =>
      k x s * l s y * f y) (μ.prod μ) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry fun s y =>
        k x s * l s y * f y) (μ.prod μ) := by
      exact (hxk.aestronglyMeasurable.comp_fst.mul
        hl.aestronglyMeasurable).mul
          (Lp.aestronglyMeasurable f).comp_snd
    apply (integrable_prod_iff' hmeas).2
    constructor
    · filter_upwards [hlCol] with y hyl
      exact (hxk.integrable_mul hyl).mul_const (f y)
    · have hnormEq : (fun y => ∫ s,
          ‖k x s * l s y * f y‖ ∂μ) =ᵐ[μ]
          fun y => ‖m x y * f y‖ := by
        filter_upwards [hP, hlCol] with y hyP hyl
        have hmxy : 0 ≤ m x y := by
          rw [← hconv x y hxP hyP]
          exact integral_nonneg_of_ae <|
            hP.mono fun z hz =>
              mul_nonneg (hk_nonneg x z hxP hz)
                (hl_nonneg z y hz hyP)
        calc
          (∫ s, ‖k x s * l s y * f y‖ ∂μ) =
              ∫ s, (k x s * l s y) * |f y| ∂μ := by
            apply integral_congr_ae
            filter_upwards [hP] with s hsP
            rw [Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (mul_nonneg
                (hk_nonneg x s hxP hsP)
                (hl_nonneg s y hsP hyP))]
          _ = (∫ s, k x s * l s y ∂μ) * |f y| := by
            rw [integral_mul_const]
          _ = m x y * |f y| := by rw [hconv x y hxP hyP]
          _ = ‖m x y * f y‖ := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hmxy]
      have hnormInt := (hxm.integrable_mul (Lp.memLp f)).norm
      exact hnormInt.congr hnormEq.symm
  calc
    (∫ s, k x s *
        (operator (hl.toLp (Function.uncurry l)) f) s ∂μ) =
        ∫ s, k x s * (∫ y, l s y * f y ∂μ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hinner] with s hs
      rw [hs]
    _ = ∫ s, ∫ y, k x s * l s y * f y ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = ∫ y, ∫ s, k x s * l s y * f y ∂μ ∂μ :=
      integral_integral_swap hdouble
    _ = ∫ y, m x y * f y ∂μ := by
      apply integral_congr_ae
      filter_upwards [hP] with y hyP
      calc
        (∫ s, k x s * l s y * f y ∂μ) =
            (∫ s, k x s * l s y ∂μ) * f y := by
          rw [← integral_mul_const]
        _ = m x y * f y := by rw [hconv x y hxP hyP]

end HBL.L2Kernel
