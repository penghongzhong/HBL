import HBL.RetainedThresholdBackward

/-!
Exact tail estimates for a retained threshold feedback source E(t)a(t).
The threshold rate loses one power, as proved in RetainedThresholdBackward.
A primitive operator bound of order t^(-nu), nu>2, compensates that loss.
This file does not assert that the physical differentiated residual has
this bound, nor construct the centre propagator. It proves the entire
conditional tail estimate, including integrability and late-time smallness.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.TriangularRepair

abbrev FeedbackEnergySpace := FullRadialEnergyL2 × FullRadialEnergyL2

/-- Actual Bochner tail of the feedback source, before centre propagation. -/
def retainedFeedbackTail
    (E : ℝ → (ℝ × ℝ) →L[ℝ] FeedbackEnergySpace)
    (a : ℝ → ℝ × ℝ) (s : ℝ) : FeedbackEnergySpace :=
  -(∫ t in Ioi s, E t (a t))

/-- Weighted smallness factor. Its limit at infinity is proved below. -/
def retainedFeedbackSmallness (p nu L A C s : ℝ) : ℝ :=
  (L * A) / (p + nu - 2) * s ^ (2 - nu) +
    (L * C) / (p + nu - 1) * s ^ (1 - nu)

private theorem feedback_source_bound
    {E : ℝ → (ℝ × ℝ) →L[ℝ] FeedbackEnergySpace}
    {a : ℝ → ℝ × ℝ} {p nu L A C t : ℝ}
    (ht : 0 < t) (hL : 0 ≤ L)
    (hE : ‖E t‖ ≤ L * t ^ (-nu))
    (ha : ‖a t‖ ≤ A * t ^ (1 - p) + C * t ^ (-p)) :
    ‖E t (a t)‖ ≤ (L * A) * t ^ (1 - p - nu) +
      (L * C) * t ^ (-p - nu) := by
  have h1 : t ^ (-nu) * t ^ (1 - p) = t ^ (1 - p - nu) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have h2 : t ^ (-nu) * t ^ (-p) = t ^ (-p - nu) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  calc
    ‖E t (a t)‖ ≤ ‖E t‖ * ‖a t‖ := (E t).le_opNorm _
    _ ≤ (L * t ^ (-nu)) * (A * t ^ (1 - p) + C * t ^ (-p)) :=
      mul_le_mul hE ha (norm_nonneg _) (mul_nonneg hL (Real.rpow_nonneg ht.le _))
    _ = (L * A) * (t ^ (-nu) * t ^ (1 - p)) +
          (L * C) * (t ^ (-nu) * t ^ (-p)) := by ring
    _ = _ := by rw [h1, h2]

private theorem feedback_integrable
    {E : ℝ → (ℝ × ℝ) →L[ℝ] FeedbackEnergySpace}
    {a : ℝ → ℝ × ℝ} {s0 p nu L A C : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu) (hL : 0 ≤ L)
    (hEc : ContinuousOn E (Ici s0)) (hac : ContinuousOn a (Ici s0))
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (ha : ∀ t, s0 ≤ t → ‖a t‖ ≤ A * t ^ (1 - p) + C * t ^ (-p)) :
    IntegrableOn (fun t => E t (a t)) (Ioi s0) := by
  have hc : ContinuousOn (fun t => E t (a t)) (Ioi s0) :=
    (hEc.clm_apply hac).mono Ioi_subset_Ici_self
  have hi := ((integrableOn_Ioi_rpow_of_lt
    (show 1 - p - nu < -1 by linarith) hs0).const_mul (L * A)).add
    ((integrableOn_Ioi_rpow_of_lt
      (show -p - nu < -1 by linarith) hs0).const_mul (L * C))
  apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact feedback_source_bound (hs0.trans ht) hL (hE t ht.le) (ha t ht.le)

private theorem feedback_tail_bound
    {E : ℝ → (ℝ × ℝ) →L[ℝ] FeedbackEnergySpace}
    {a : ℝ → ℝ × ℝ} {s0 p nu L A C s : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu) (hL : 0 ≤ L)
    (hEc : ContinuousOn E (Ici s0)) (hac : ContinuousOn a (Ici s0))
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (ha : ∀ t, s0 ≤ t → ‖a t‖ ≤ A * t ^ (1 - p) + C * t ^ (-p))
    (hs : s0 ≤ s) :
    ‖retainedFeedbackTail E a s‖ ≤
      (L * A) / (p + nu - 2) * s ^ (2 - p - nu) +
        (L * C) / (p + nu - 1) * s ^ (1 - p - nu) := by
  have hsp := hs0.trans_le hs
  have hi := (feedback_integrable hs0 hp hnu hL hEc hac hE ha).mono_set
    (Ioi_subset_Ioi hs)
  have hi1 := (integrableOn_Ioi_rpow_of_lt
    (show 1 - p - nu < -1 by linarith) hsp).const_mul (L * A)
  have hi2 := (integrableOn_Ioi_rpow_of_lt
    (show -p - nu < -1 by linarith) hsp).const_mul (L * C)
  have hI1 : (∫ t in Ioi s, t ^ (1 - p - nu)) =
      s ^ (2 - p - nu) / (p + nu - 2) := by
    have h1 : -1 - (p + nu - 2) = 1 - p - nu := by ring
    have h2 : -(p + nu - 2) = 2 - p - nu := by ring
    simpa only [h1, h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀ := s) (δ := p + nu - 2) hsp (by linarith))
  have hI2 : (∫ t in Ioi s, t ^ (-p - nu)) =
      s ^ (1 - p - nu) / (p + nu - 1) := by
    have h1 : -1 - (p + nu - 1) = -p - nu := by ring
    have h2 : -(p + nu - 1) = 1 - p - nu := by ring
    simpa only [h1, h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀ := s) (δ := p + nu - 1) hsp (by linarith))
  unfold retainedFeedbackTail
  rw [norm_neg]
  calc
    ‖∫ t in Ioi s, E t (a t)‖ ≤ ∫ t in Ioi s, ‖E t (a t)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi s, (L * A) * t ^ (1 - p - nu) +
        (L * C) * t ^ (-p - nu) := by
      apply integral_mono_ae hi.norm (hi1.add hi2)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact feedback_source_bound (hsp.trans ht) hL
        (hE t (hs.trans ht.le)) (ha t (hs.trans ht.le))
    _ = _ := by
      rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul, hI1, hI2]
      ring

private theorem feedback_weighted_bound
    {E : ℝ → (ℝ × ℝ) →L[ℝ] FeedbackEnergySpace}
    {a : ℝ → ℝ × ℝ} {s0 p nu L A C s : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hEc : ContinuousOn E (Ici s0)) (hac : ContinuousOn a (Ici s0))
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (ha : ∀ t, s0 ≤ t → ‖a t‖ ≤ A * t ^ (1 - p) + C * t ^ (-p))
    (hs : s0 ≤ s) :
    ‖retainedFeedbackTail E a s‖ ≤ retainedFeedbackSmallness p nu L A C s0 * s ^ (-p) := by
  have hsp := hs0.trans_le hs
  have h1 : s ^ (2 - p - nu) = s ^ (2 - nu) * s ^ (-p) := by
    rw [← Real.rpow_add hsp]
    congr 1
    ring
  have h2 : s ^ (1 - p - nu) = s ^ (1 - nu) * s ^ (-p) := by
    rw [← Real.rpow_add hsp]
    congr 1
    ring
  have hsmall : retainedFeedbackSmallness p nu L A C s ≤
      retainedFeedbackSmallness p nu L A C s0 := by
    unfold retainedFeedbackSmallness
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hs0 hs (show 2 - nu ≤ 0 by linarith))
        (div_nonneg (mul_nonneg hL hA) (by linarith)))
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hs0 hs (show 1 - nu ≤ 0 by linarith))
        (div_nonneg (mul_nonneg hL hC) (by linarith)))
  calc
    ‖retainedFeedbackTail E a s‖ ≤
        (L * A) / (p + nu - 2) * s ^ (2 - p - nu) +
          (L * C) / (p + nu - 1) * s ^ (1 - p - nu) :=
      feedback_tail_bound hs0 hp hnu hL hEc hac hE ha hs
    _ = retainedFeedbackSmallness p nu L A C s * s ^ (-p) := by
      rw [h1, h2]
      unfold retainedFeedbackSmallness
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hsp.le _)

/-- Complete feedback-tail criterion for the one-power-loss threshold
rate. Actual convergence and the small late-time factor are conclusions.
The bound on E is an explicit input, not claimed proved for the PDE. -/
theorem retainedFeedbackTail_certified
    (E : ℝ → (ℝ × ℝ) →L[ℝ] FeedbackEnergySpace)
    (a : ℝ → ℝ × ℝ) (s0 p nu L A C : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hEc : ContinuousOn E (Ici s0)) (hac : ContinuousOn a (Ici s0))
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (ha : ∀ t, s0 ≤ t → ‖a t‖ ≤ A * t ^ (1 - p) + C * t ^ (-p)) :
    (∀ s, s0 ≤ s → IntegrableOn (fun t => E t (a t)) (Ioi s)) ∧
    (∀ s, s0 ≤ s → ‖retainedFeedbackTail E a s‖ ≤
      (L * A) / (p + nu - 2) * s ^ (2 - p - nu) +
        (L * C) / (p + nu - 1) * s ^ (1 - p - nu)) ∧
    (∀ s, s0 ≤ s → ‖retainedFeedbackTail E a s‖ ≤
      retainedFeedbackSmallness p nu L A C s0 * s ^ (-p)) ∧
    Tendsto (retainedFeedbackSmallness p nu L A C) atTop (𝓝 0) := by
  refine ⟨(fun s hs => (feedback_integrable hs0 hp hnu hL hEc hac hE ha).mono_set
    (Ioi_subset_Ioi hs)),
    (fun s hs => feedback_tail_bound hs0 hp hnu hL hEc hac hE ha hs),
    (fun s hs => feedback_weighted_bound hs0 hp hnu hL hA hC hEc hac hE ha hs), ?_⟩
  have h1 : Tendsto (fun s : ℝ => (L * A) / (p + nu - 2) * s ^ (2 - nu))
      atTop (𝓝 0) := by
    have he : -(nu - 2) = 2 - nu := by ring
    simpa only [he, mul_zero] using
      (tendsto_rpow_neg_atTop (show 0 < nu - 2 by linarith)).const_mul
        ((L * A) / (p + nu - 2))
  have h2 : Tendsto (fun s : ℝ => (L * C) / (p + nu - 1) * s ^ (1 - nu))
      atTop (𝓝 0) := by
    have he : -(nu - 1) = 1 - nu := by ring
    simpa only [he, mul_zero] using
      (tendsto_rpow_neg_atTop (show 0 < nu - 1 by linarith)).const_mul
        ((L * C) / (p + nu - 1))
  change Tendsto (fun s : ℝ => (L * A) / (p + nu - 2) * s ^ (2 - nu) +
    (L * C) / (p + nu - 1) * s ^ (1 - nu)) atTop (𝓝 0)
  simpa only [add_zero] using h1.add h2

end HBL.Modulation.TriangularRepair
