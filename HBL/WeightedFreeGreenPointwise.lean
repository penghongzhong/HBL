import HBL.WeightedFreeGreen

/-!
Pointwise representatives for the weighted free Green operator.

The Hilbert--Schmidt construction in `WeightedFreeGreen` deliberately
defines the operator weakly.  For the spectral bridge one also needs its
canonical continuous representative.  This file constructs that
representative directly and proves that it agrees almost everywhere with
the abstract L2 operator.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- The one-sided weight occurring in the unweighted Green source. -/
def weightedGreenDecay (r : ℝ) : ℝ := (1 + r ^ 2)⁻¹

theorem weightedGreenDecay_continuous : Continuous weightedGreenDecay := by
  unfold weightedGreenDecay
  exact (continuous_const.add (continuous_id.pow 2)).inv₀
    (fun r => by dsimp; positivity)

theorem weightedGreenDecay_nonneg (r : ℝ) : 0 ≤ weightedGreenDecay r := by
  unfold weightedGreenDecay
  positivity

theorem weightedGreenDecay_memLp_two :
    MemLp weightedGreenDecay 2 halfLineMeasure := by
  apply (memLp_two_iff_integrable_sq
    weightedGreenDecay_continuous.aestronglyMeasurable.restrict).2
  have h : IntegrableOn (fun r : ℝ => (1 + r ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  refine h.mono'
    (weightedGreenDecay_continuous.pow 2).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold weightedGreenDecay
  have ha0 : 0 ≤ (1 + r ^ 2)⁻¹ := by positivity
  have ha1 : (1 + r ^ 2)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity : 0 < 1 + r ^ 2)).2
      (by nlinarith [sq_nonneg r])
  nlinarith [mul_self_le_mul_self ha0 ha1]

/-- Multiplication by the Green weight turns every half-line L2 datum into
an L1 source. -/
theorem weightedGreen_source_integrable
    (f : RealL2 halfLineMeasure) :
    Integrable (fun r : ℝ => weightedGreenDecay r * f r)
      halfLineMeasure := by
  exact weightedGreenDecay_memLp_two.integrable_mul (Lp.memLp f)

/-- The L1 norm of the weighted source, packaged as a nonnegative real. -/
def weightedGreenLipschitzConstant
    (f : RealL2 halfLineMeasure) : NNReal where
  val := ∫ rho : ℝ, ‖weightedGreenDecay rho * f rho‖
    ∂halfLineMeasure
  property := integral_nonneg fun _ => norm_nonneg _

/-- The unweighted zero-slope Green integral associated with an L2 datum. -/
def weightedGreenPrimitive
    (f : RealL2 halfLineMeasure) (r : ℝ) : ℝ :=
  ∫ rho : ℝ, min r rho * (weightedGreenDecay rho * f rho)
    ∂halfLineMeasure

theorem weightedGreenPrimitive_integrable_kernel
    (f : RealL2 halfLineMeasure) (r : ℝ) :
    Integrable (fun rho : ℝ =>
      min r rho * (weightedGreenDecay rho * f rho))
      halfLineMeasure := by
  have hsrc := weightedGreen_source_integrable f
  have hmajor : Integrable (fun rho : ℝ =>
      |r| * ‖weightedGreenDecay rho * f rho‖) halfLineMeasure :=
    hsrc.norm.const_mul |r|
  refine hmajor.mono' ?_ ?_
  · exact (continuous_const.min continuous_id).aestronglyMeasurable.mul
      (weightedGreenDecay_continuous.aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hρ
    have hmin : |min r rho| ≤ |r| := by
      by_cases hr : r ≤ rho
      · rw [min_eq_left hr]
      · have hρr : rho < r := lt_of_not_ge hr
        rw [min_eq_right hρr.le]
        rw [abs_of_pos hρ, abs_of_pos (hρ.trans hρr)]
        exact hρr.le
    calc
      ‖min r rho * (weightedGreenDecay rho * f rho)‖ =
          |min r rho| * ‖weightedGreenDecay rho * f rho‖ := by
        simp only [Real.norm_eq_abs, abs_mul]
      _ ≤ |r| * ‖weightedGreenDecay rho * f rho‖ :=
        mul_le_mul_of_nonneg_right hmin (norm_nonneg _)

theorem weightedGreenPrimitive_lipschitz
    (f : RealL2 halfLineMeasure) :
    LipschitzWith (weightedGreenLipschitzConstant f)
      (weightedGreenPrimitive f) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  rw [Real.dist_eq]
  unfold weightedGreenPrimitive
  have hr := weightedGreenPrimitive_integrable_kernel f r
  have hs := weightedGreenPrimitive_integrable_kernel f s
  rw [← integral_sub hr hs]
  calc
    |∫ rho : ℝ,
        (min r rho * (weightedGreenDecay rho * f rho) -
          min s rho * (weightedGreenDecay rho * f rho))
        ∂halfLineMeasure| ≤
        ∫ rho : ℝ,
          ‖min r rho * (weightedGreenDecay rho * f rho) -
            min s rho * (weightedGreenDecay rho * f rho)‖
          ∂halfLineMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ rho : ℝ,
          |r - s| * ‖weightedGreenDecay rho * f rho‖
          ∂halfLineMeasure := by
      apply integral_mono_ae
      · exact (hr.sub hs).norm
      · exact (weightedGreen_source_integrable f).norm.const_mul |r - s|
      · filter_upwards with rho
        rw [← sub_mul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (abs_min_sub_min_le_max r rho s rho |>.trans_eq (by simp))
          (abs_nonneg _)
    _ = |r - s| *
          ∫ rho : ℝ, ‖weightedGreenDecay rho * f rho‖
            ∂halfLineMeasure := by rw [integral_const_mul]
    _ = ↑(weightedGreenLipschitzConstant f) * dist r s := by
      rw [Real.dist_eq]
      change |r - s| *
          (∫ rho : ℝ, ‖weightedGreenDecay rho * f rho‖ ∂halfLineMeasure) =
        (∫ rho : ℝ, ‖weightedGreenDecay rho * f rho‖ ∂halfLineMeasure) *
          |r - s|
      exact mul_comm _ _

theorem weightedGreenPrimitive_continuous
    (f : RealL2 halfLineMeasure) :
    Continuous (weightedGreenPrimitive f) :=
  (weightedGreenPrimitive_lipschitz f).continuous

/-- Canonical continuous representative of the weighted Green output. -/
def weightedFreeGreenPointwise
    (f : RealL2 halfLineMeasure) (r : ℝ) : ℝ :=
  weightedGreenDecay r * weightedGreenPrimitive f r

theorem weightedFreeGreenPointwise_continuous
    (f : RealL2 halfLineMeasure) :
    Continuous (weightedFreeGreenPointwise f) :=
  weightedGreenDecay_continuous.mul (weightedGreenPrimitive_continuous f)

theorem weightedFreeGreen_eq_decay_primitive
    (f : RealL2 halfLineMeasure) (r : ℝ) :
    (∫ rho : ℝ, weightedFreeGreen r rho * f rho
      ∂halfLineMeasure) = weightedFreeGreenPointwise f r := by
  unfold weightedFreeGreenPointwise weightedGreenPrimitive
    weightedFreeGreen weightedGreenDecay
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with rho
  ring

/-- A square-integrable majorant for the continuous Green representative. -/
def weightedGreenOutputMajorant (r : ℝ) : ℝ :=
  |r| * weightedGreenDecay r

theorem weightedGreenOutputMajorant_memLp_two :
    MemLp weightedGreenOutputMajorant 2 halfLineMeasure := by
  have hm : AEStronglyMeasurable weightedGreenOutputMajorant
      halfLineMeasure :=
    (continuous_abs.mul weightedGreenDecay_continuous).aestronglyMeasurable.restrict
  apply (memLp_two_iff_integrable_sq hm).2
  refine integrable_inv_one_add_sq.integrableOn.mono' ?_ ?_
  · exact ((continuous_abs.mul weightedGreenDecay_continuous).pow 2).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      weightedGreenOutputMajorant, mul_pow, sq_abs,
      weightedGreenDecay]
    have hden : 0 < 1 + r ^ 2 := by positivity
    calc
      r ^ 2 * (1 + r ^ 2)⁻¹ ^ 2 ≤
          (1 + r ^ 2) * (1 + r ^ 2)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg r]) (sq_nonneg _)
      _ = (1 + r ^ 2)⁻¹ := by field_simp

theorem weightedFreeGreenPointwise_memLp_two
    (f : RealL2 halfLineMeasure) :
    MemLp (weightedFreeGreenPointwise f) 2 halfLineMeasure := by
  let C : ℝ := ∫ rho : ℝ, ‖weightedGreenDecay rho * f rho‖
    ∂halfLineMeasure
  refine (weightedGreenOutputMajorant_memLp_two.const_mul C).mono'
    (weightedFreeGreenPointwise_continuous f).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs]
  have hq : |weightedGreenPrimitive f r| ≤ C * |r| := by
    unfold weightedGreenPrimitive C
    calc
      |∫ rho : ℝ, min r rho *
          (weightedGreenDecay rho * f rho) ∂halfLineMeasure| ≤
          ∫ rho : ℝ, ‖min r rho *
            (weightedGreenDecay rho * f rho)‖ ∂halfLineMeasure :=
        abs_integral_le_integral_abs
      _ ≤ ∫ rho : ℝ, |r| *
          ‖weightedGreenDecay rho * f rho‖ ∂halfLineMeasure := by
        apply integral_mono_ae
        · exact (weightedGreenPrimitive_integrable_kernel f r).norm
        · exact (weightedGreen_source_integrable f).norm.const_mul |r|
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hρ
          rw [Real.norm_eq_abs, abs_mul]
          have hmin : |min r rho| ≤ |r| := by
            have hminpos : 0 < min r rho := lt_min hr hρ
            rw [abs_of_pos hminpos, abs_of_pos hr]
            exact min_le_left _ _
          exact mul_le_mul_of_nonneg_right hmin (abs_nonneg _)
      _ = C * |r| := by rw [integral_const_mul]; ring
  unfold weightedFreeGreenPointwise weightedGreenOutputMajorant
  rw [abs_mul, abs_of_nonneg (weightedGreenDecay_nonneg r)]
  calc
    weightedGreenDecay r * |weightedGreenPrimitive f r| ≤
        weightedGreenDecay r * (C * |r|) :=
      mul_le_mul_of_nonneg_left hq (weightedGreenDecay_nonneg r)
    _ = |C * (|r| * weightedGreenDecay r)| := by
      have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
      rw [abs_mul, abs_of_nonneg hC, abs_mul, abs_abs,
        abs_of_nonneg (weightedGreenDecay_nonneg r)]
      ring
    _ = C * weightedGreenOutputMajorant r := by
      have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
      rw [abs_of_nonneg (mul_nonneg hC (mul_nonneg (abs_nonneg _)
        (weightedGreenDecay_nonneg r)))]
      rfl

/-- The weak Hilbert--Schmidt Green operator equals its canonical
continuous integral representative almost everywhere. -/
theorem weightedFreeGreenOperator_ae_pointwise
    (f : RealL2 halfLineMeasure) :
    (weightedFreeGreenOperator f : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedFreeGreenPointwise f := by
  let h : RealL2 halfLineMeasure :=
    (weightedFreeGreenPointwise_memLp_two f).toLp
      (weightedFreeGreenPointwise f)
  have hh_ae : (h : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedFreeGreenPointwise f :=
    (weightedFreeGreenPointwise_memLp_two f).coeFn_toLp
  have hop : weightedFreeGreenOperator f = h := by
    apply ext_inner_right ℝ
    intro g
    have hprod : Integrable (fun p : ℝ × ℝ =>
        weightedFreeGreen p.1 p.2 * (g p.1 * f p.2))
        (halfLineMeasure.prod halfLineMeasure) := by
      have hK := weightedFreeGreen_memLp_two
      have ht := Lp.memLp (tensor g f)
      have h := hK.integrable_mul ht
      refine h.congr ?_
      filter_upwards [tensor_ae g f] with p hp
      change weightedFreeGreen p.1 p.2 * (tensor g f : ℝ × ℝ → ℝ) p = _
      rw [hp]
    calc
      inner ℝ (weightedFreeGreenOperator f) g =
          inner ℝ weightedFreeGreenL2 (tensor g f) :=
        inner_operator _ _ _
      _ = ∫ p : ℝ × ℝ,
          weightedFreeGreen p.1 p.2 * (g p.1 * f p.2)
          ∂(halfLineMeasure.prod halfLineMeasure) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [weightedFreeGreenL2_ae, tensor_ae g f]
          with p hK ht
        rw [hK, ht, Real.inner_apply]
        rfl
      _ = ∫ r : ℝ, ∫ rho : ℝ,
          weightedFreeGreen r rho * (g r * f rho)
          ∂halfLineMeasure ∂halfLineMeasure :=
        integral_prod _ hprod
      _ = ∫ r : ℝ, weightedFreeGreenPointwise f r * g r
          ∂halfLineMeasure := by
        apply integral_congr_ae
        filter_upwards with r
        rw [show (∫ rho : ℝ,
            weightedFreeGreen r rho * (g r * f rho)
            ∂halfLineMeasure) = g r *
              (∫ rho : ℝ, weightedFreeGreen r rho * f rho
                ∂halfLineMeasure) by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with rho
          ring,
          weightedFreeGreen_eq_decay_primitive]
        ring
      _ = inner ℝ h g := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hh_ae] with r hh
        rw [hh, Real.inner_apply]
  rw [hop]
  exact hh_ae

end HBL.Modulation.Monopole
