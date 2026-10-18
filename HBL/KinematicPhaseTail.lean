import HBL.KinematicPhysicalRateError

/-! Quantitative phase tails against a positive linearly growing clock. -/

noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology
namespace HBL.Kinematic

theorem phaseQuotient_abs_le {q g : ℝ → ℝ} {s c J δ : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hq : c * s ≤ q s)
    (hg : |g s| ≤ J * s ^ (-δ)) :
    |g s / q s| ≤ (J / c) * s ^ (-1 - δ) := by
  have hqp : 0 < q s := (mul_pos hc hs).trans_le hq
  have hp : s ^ (-δ) / s = s ^ (-1 - δ) := by
    rw [← Real.rpow_sub_one hs.ne']
    congr 1
    ring
  rw [abs_div, abs_of_pos hqp]
  calc
    |g s| / q s ≤ (J * s ^ (-δ)) / q s :=
      div_le_div_of_nonneg_right hg hqp.le
    _ ≤ (J * s ^ (-δ)) / (c * s) :=
      div_le_div_of_nonneg_left ((abs_nonneg _).trans hg) (mul_pos hc hs) hq
    _ = (J / c) * (s ^ (-δ) / s) := by field_simp
    _ = _ := by rw [hp]

theorem phaseQuotient_integrableOn {q g : ℝ → ℝ} {s₀ c J δ : ℝ}
    (hs₀ : 0 < s₀) (hδ : 0 < δ) (hc : 0 < c)
    (hqcont : ContinuousOn q (Ioi s₀)) (hgcont : ContinuousOn g (Ioi s₀))
    (hq : ∀ s ∈ Ioi s₀, c * s ≤ q s)
    (hg : ∀ s ∈ Ioi s₀, |g s| ≤ J * s ^ (-δ)) :
    IntegrableOn (fun s => g s / q s) (Ioi s₀) := by
  have hmeas : AEStronglyMeasurable (fun s => g s / q s)
      (volume.restrict (Ioi s₀)) :=
    (hgcont.div hqcont (fun s hs =>
      ((mul_pos hc (hs₀.trans hs)).trans_le (hq s hs)).ne')).aestronglyMeasurable
      measurableSet_Ioi
  have hi := (integrableOn_Ioi_rpow_of_lt
    (show -1 - δ < -1 by linarith) hs₀).const_mul (J / c)
  apply hi.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact phaseQuotient_abs_le (hs₀.trans hs) hc (hq s hs) (hg s hs)

theorem phaseQuotient_tail_abs_le {q g : ℝ → ℝ} {s₀ s c J δ : ℝ}
    (hs₀ : 0 < s₀) (hδ : 0 < δ) (hc : 0 < c)
    (hqcont : ContinuousOn q (Ioi s₀)) (hgcont : ContinuousOn g (Ioi s₀))
    (hq : ∀ t ∈ Ioi s₀, c * t ≤ q t)
    (hg : ∀ t ∈ Ioi s₀, |g t| ≤ J * t ^ (-δ)) (hs : s₀ ≤ s) :
    |∫ t in Ioi s, g t / q t| ≤ (J / c) * (s ^ (-δ) / δ) := by
  have hspos := hs₀.trans_le hs
  have hi := (phaseQuotient_integrableOn hs₀ hδ hc hqcont hgcont hq hg).mono_set
    (Ioi_subset_Ioi hs)
  have hb := (integrableOn_Ioi_rpow_of_lt
    (show -1 - δ < -1 by linarith) hspos).const_mul (J / c)
  calc
    |∫ t in Ioi s, g t / q t| ≤ ∫ t in Ioi s, |g t / q t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi s, (J / c) * t ^ (-1 - δ) := by
      apply integral_mono_ae hi.abs hb
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact phaseQuotient_abs_le (hspos.trans ht) hc (hq t (hs.trans_lt ht))
        (hg t (hs.trans_lt ht))
    _ = _ := by rw [integral_const_mul, integral_Ioi_rpow_neg_one_sub hspos hδ]

theorem phaseQuotient_tail_isBigO {q g : ℝ → ℝ} {s₀ c J δ : ℝ}
    (hs₀ : 0 < s₀) (hδ : 0 < δ) (hc : 0 < c)
    (hqcont : ContinuousOn q (Ioi s₀)) (hgcont : ContinuousOn g (Ioi s₀))
    (hq : ∀ t ∈ Ioi s₀, c * t ≤ q t)
    (hg : ∀ t ∈ Ioi s₀, |g t| ≤ J * t ^ (-δ)) :
    (fun s => ∫ t in Ioi s, g t / q t) =O[atTop] (fun s => s ^ (-δ)) := by
  apply IsBigO.of_bound (J / c / δ)
  filter_upwards [eventually_ge_atTop s₀] with s hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (hs₀.trans_le hs).le _)]
  exact (phaseQuotient_tail_abs_le hs₀ hδ hc hqcont hgcont hq hg hs).trans_eq (by ring)

end HBL.Kinematic
