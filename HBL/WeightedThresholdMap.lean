import HBL.WeightedBackwardPaths
import HBL.KinematicTailEstimates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# The actual weighted threshold tail map

For a bounded continuous centre path qhat, recover
  q(s)=s^{-p} qhat(s)
and define the terminal threshold coordinate
  a(s)=-∫_s^∞ B q(t) dt.
After multiplying by s^{p-1}, this is a bounded continuous path.  The map
qhat -> ahat is genuinely Lipschitz with constant ‖B‖/(p-1).

This is the finite-dimensional half of the repaired HBL joint contraction.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.MainBackward

def weightedThresholdSource
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (q : CenterWeightedPath s0 p) (t : ℝ) : ℝ × ℝ :=
  B (unweightPathGlobal p s0 q t)

def weightedThresholdTail
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (q : CenterWeightedPath s0 p) (s : ℝ) : ℝ × ℝ :=
  -(∫ t in Ioi s, weightedThresholdSource B s0 p q t)

theorem weightedThresholdSource_continuous
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0)
    (q : CenterWeightedPath s0 p) :
    Continuous (weightedThresholdSource B s0 p q) := by
  exact B.continuous.comp (unweightPathGlobal_continuous p s0 hs0 q)

private theorem weightedThresholdSource_bound
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0)
    (q : CenterWeightedPath s0 p)
    {t : ℝ} (ht : s0 ≤ t) :
    ‖weightedThresholdSource B s0 p q t‖ ≤
      (‖B‖ * ‖q‖) * t ^ (-p) := by
  calc
    ‖weightedThresholdSource B s0 p q t‖
        ≤ ‖B‖ * ‖unweightPathGlobal p s0 q t‖ := B.le_opNorm _
    _ ≤ ‖B‖ * (‖q‖ * t ^ (-p)) := by
      exact mul_le_mul_of_nonneg_left
        (unweightPathGlobal_norm_bound p s0 hs0 q ht) (norm_nonneg B)
    _ = (‖B‖ * ‖q‖) * t ^ (-p) := by ring

theorem weightedThresholdSource_integrable
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q : CenterWeightedPath s0 p) :
    IntegrableOn (weightedThresholdSource B s0 p q) (Ioi s0) := by
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-p)) (Ioi s0) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hs0
  have hmajor := hpow.const_mul (‖B‖ * ‖q‖)
  have hmeas :
      AEStronglyMeasurable (weightedThresholdSource B s0 p q)
        (volume.restrict (Ioi s0)) :=
    (weightedThresholdSource_continuous B s0 p hs0 q).aestronglyMeasurable.restrict
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact weightedThresholdSource_bound B s0 p hs0 q ht.le

private theorem weightedThresholdTail_eq_fixed
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q : CenterWeightedPath s0 p)
    {s : ℝ} (hs : s0 ≤ s) :
    weightedThresholdTail B s0 p q s =
      -(∫ t in Ioi s0, weightedThresholdSource B s0 p q t) +
        ∫ t in s0..s, weightedThresholdSource B s0 p q t := by
  have hi := weightedThresholdSource_integrable B s0 p hs0 hp q
  have h := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi hs))
  unfold weightedThresholdTail
  rw [← h]
  abel

theorem weightedThresholdTail_continuousOn
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q : CenterWeightedPath s0 p) :
    ContinuousOn (weightedThresholdTail B s0 p q) (Ici s0) := by
  have hscont := weightedThresholdSource_continuous B s0 p hs0 q
  have hc : Continuous
      (fun s =>
        -(∫ t in Ioi s0, weightedThresholdSource B s0 p q t) +
          ∫ t in s0..s, weightedThresholdSource B s0 p q t) :=
    continuous_const.add
      (intervalIntegral.differentiable_integral_of_continuous hscont).continuous
  apply hc.continuousOn.congr
  intro s hs
  exact weightedThresholdTail_eq_fixed B s0 p hs0 hp q hs

theorem weightedThresholdTail_bound
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q : CenterWeightedPath s0 p)
    {s : ℝ} (hs : s0 ≤ s) :
    ‖weightedThresholdTail B s0 p q s‖ ≤
      (‖B‖ * ‖q‖) / (p - 1) * s ^ (1 - p) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hi := (weightedThresholdSource_integrable B s0 p hs0 hp q).mono_set
    (Ioi_subset_Ioi hs)
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-p)) (Ioi s) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hsp
  have hmajor := hpow.const_mul (‖B‖ * ‖q‖)
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi s),
      ‖weightedThresholdSource B s0 p q t‖ ≤
        (‖B‖ * ‖q‖) * t ^ (-p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact weightedThresholdSource_bound B s0 p hs0 q (hs.trans ht.le)
  have hI : (∫ t in Ioi s, t ^ (-p)) =
      s ^ (1 - p) / (p - 1) := by
    have h1 : -1 - (p - 1) = -p := by ring
    have h2 : -(p - 1) = 1 - p := by ring
    simpa only [h1, h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀ := s) (δ := p - 1) hsp (by linarith))
  unfold weightedThresholdTail
  rw [norm_neg]
  calc
    ‖∫ t in Ioi s, weightedThresholdSource B s0 p q t‖
        ≤ ∫ t in Ioi s, (‖B‖ * ‖q‖) * t ^ (-p) :=
          norm_integral_le_of_norm_le hmajor hpoint
    _ = (‖B‖ * ‖q‖) * (s ^ (1 - p) / (p - 1)) := by
      rw [integral_const_mul, hI]
    _ = (‖B‖ * ‖q‖) / (p - 1) * s ^ (1 - p) := by ring

def weightedThresholdValue
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (q : CenterWeightedPath s0 p)
    (s : LateTime s0) : ℝ × ℝ :=
  ((s : ℝ) ^ (p - 1)) • weightedThresholdTail B s0 p q s

theorem weightedThresholdValue_continuous
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q : CenterWeightedPath s0 p) :
    Continuous (weightedThresholdValue B s0 p q) := by
  have htail :
      Continuous (fun s : LateTime s0 => weightedThresholdTail B s0 p q s) :=
    (weightedThresholdTail_continuousOn B s0 p hs0 hp q).domRestrict
  apply continuous_iff_continuousAt.2
  intro s
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have hpow :
      ContinuousAt (fun t : LateTime s0 => ((t : ℝ) ^ (p - 1))) s := by
    exact (Real.continuousAt_rpow_const (s : ℝ) (p - 1)
      (Or.inl hspos.ne')).comp continuousAt_subtype_val
  exact hpow.smul htail.continuousAt

theorem weightedThresholdValue_bound
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q : CenterWeightedPath s0 p)
    (s : LateTime s0) :
    ‖weightedThresholdValue B s0 p q s‖ ≤
      (‖B‖ / (p - 1)) * ‖q‖ := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have ht := weightedThresholdTail_bound B s0 p hs0 hp q s.2
  unfold weightedThresholdValue
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hspos _)]
  have hpow :
      (s : ℝ) ^ (p - 1) * (s : ℝ) ^ (1 - p) = 1 := by
    rw [← Real.rpow_add hspos]
    norm_num
  have hnon : 0 ≤ (s : ℝ) ^ (p - 1) :=
    (Real.rpow_pos_of_pos hspos _).le
  calc
    (s : ℝ) ^ (p - 1) * ‖weightedThresholdTail B s0 p q s‖
        ≤ (s : ℝ) ^ (p - 1) *
          ((‖B‖ * ‖q‖) / (p - 1) * (s : ℝ) ^ (1 - p)) :=
            mul_le_mul_of_nonneg_left ht hnon
    _ = ((‖B‖ * ‖q‖) / (p - 1)) *
          ((s : ℝ) ^ (p - 1) * (s : ℝ) ^ (1 - p)) := by ring
    _ = (‖B‖ * ‖q‖) / (p - 1) := by rw [hpow, mul_one]
    _ = (‖B‖ / (p - 1)) * ‖q‖ := by ring

def weightedThresholdMap
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p) :
    CenterWeightedPath s0 p → ThresholdWeightedPath s0 p :=
  fun q =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (weightedThresholdValue B s0 p q)
      (weightedThresholdValue_continuous B s0 p hs0 hp q)
      ((‖B‖ / (p - 1)) * ‖q‖)
      (weightedThresholdValue_bound B s0 p hs0 hp q)

theorem weightedThresholdMap_norm
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q : CenterWeightedPath s0 p) :
    ‖weightedThresholdMap B s0 p hs0 hp q‖ ≤
      (‖B‖ / (p - 1)) * ‖q‖ := by
  have hC : 0 ≤ (‖B‖ / (p - 1)) * ‖q‖ := by positivity
  rw [BoundedContinuousFunction.norm_le hC]
  intro s
  exact weightedThresholdValue_bound B s0 p hs0 hp q s

theorem weightedThresholdTail_sub
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q r : CenterWeightedPath s0 p) {s : ℝ} (hs : s0 ≤ s) :
    weightedThresholdTail B s0 p q s -
        weightedThresholdTail B s0 p r s =
      weightedThresholdTail B s0 p (q - r) s := by
  have hiq := weightedThresholdSource_integrable B s0 p hs0 hp q
  have hir := weightedThresholdSource_integrable B s0 p hs0 hp r
  unfold weightedThresholdTail weightedThresholdSource
  have hsrc :
      (fun t => B (unweightPathGlobal p s0 q t)) -
        (fun t => B (unweightPathGlobal p s0 r t)) =
      (fun t => B (unweightPathGlobal p s0 (q - r) t)) := by
    funext t
    rw [Pi.sub_apply, ← map_sub]
    simp only [unweightPathGlobal, BoundedContinuousFunction.sub_apply, smul_sub]
  have hiqs := hiq.mono_set (Ioi_subset_Ioi hs)
  have hirs := hir.mono_set (Ioi_subset_Ioi hs)
  have hInt :
      (∫ t in Ioi s, B (unweightPathGlobal p s0 q t)) -
          (∫ t in Ioi s, B (unweightPathGlobal p s0 r t)) =
        ∫ t in Ioi s, B (unweightPathGlobal p s0 (q - r) t) := by
    rw [← integral_sub hiqs hirs]
    rw [hsrc]
  rw [← hInt]
  abel

theorem weightedThresholdMap_difference_norm
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q r : CenterWeightedPath s0 p) :
    ‖weightedThresholdMap B s0 p hs0 hp q -
        weightedThresholdMap B s0 p hs0 hp r‖ ≤
      (‖B‖ / (p - 1)) * ‖q - r‖ := by
  have hC : 0 ≤ (‖B‖ / (p - 1)) * ‖q - r‖ := by positivity
  rw [BoundedContinuousFunction.norm_le hC]
  intro s
  change ‖weightedThresholdValue B s0 p q s -
      weightedThresholdValue B s0 p r s‖ ≤ _
  have htail :=
    weightedThresholdTail_bound B s0 p hs0 hp (q - r) s.2
  have hsub := weightedThresholdTail_sub B s0 p hs0 hp q r s.2
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have hval :
      weightedThresholdValue B s0 p q s -
          weightedThresholdValue B s0 p r s =
        ((s : ℝ) ^ (p - 1)) •
          weightedThresholdTail B s0 p (q - r) s := by
    unfold weightedThresholdValue
    rw [← smul_sub, hsub]
  rw [hval, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hspos _)]
  have hpow :
      (s : ℝ) ^ (p - 1) * (s : ℝ) ^ (1 - p) = 1 := by
    rw [← Real.rpow_add hspos]
    norm_num
  have hnon : 0 ≤ (s : ℝ) ^ (p - 1) :=
    (Real.rpow_pos_of_pos hspos _).le
  calc
    (s : ℝ) ^ (p - 1) *
        ‖weightedThresholdTail B s0 p (q - r) s‖
        ≤ (s : ℝ) ^ (p - 1) *
          ((‖B‖ * ‖q - r‖) / (p - 1) * (s : ℝ) ^ (1 - p)) :=
            mul_le_mul_of_nonneg_left htail hnon
    _ = ((‖B‖ * ‖q - r‖) / (p - 1)) *
          ((s : ℝ) ^ (p - 1) * (s : ℝ) ^ (1 - p)) := by ring
    _ = (‖B‖ * ‖q - r‖) / (p - 1) := by rw [hpow, mul_one]
    _ = (‖B‖ / (p - 1)) * ‖q - r‖ := by ring

theorem weightedThresholdMap_lipschitz
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p) :
    LipschitzWith (Real.toNNReal (‖B‖ / (p - 1)))
      (weightedThresholdMap B s0 p hs0 hp) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  have hnon : 0 ≤ ‖B‖ / (p - 1) := by positivity
  rw [Real.coe_toNNReal _ hnon]
  rw [dist_eq_norm, dist_eq_norm]
  exact weightedThresholdMap_difference_norm B s0 p hs0 hp q r

#print axioms weightedThresholdSource_integrable
#print axioms weightedThresholdTail_bound
#print axioms weightedThresholdMap_norm
#print axioms weightedThresholdMap_difference_norm
#print axioms weightedThresholdMap_lipschitz

end HBL.MainBackward
