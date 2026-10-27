import HBL.WeightedThresholdMap
import HBL.KinematicTailEstimates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Retained threshold self-coupling

The exact triangular equation contains the finite-dimensional term
  ell(s) E(s) a(s).
It is retained here as an actual Volterra self-feedback on the weighted
threshold path space.  No diagonalization or silent deletion is used.

If ||C(t)|| <= Lc t^{-nu}, nu > 2, and
a(t)=O(t^{1-p}), then the weighted self-feedback has Lipschitz constant
  Lc/(p+nu-2) * s0^(1-nu),
which tends to zero as s0 -> infinity.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.MainBackward

def weightedThresholdSelfSource
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (a : ThresholdWeightedPath s0 p) (t : ℝ) : ℝ × ℝ :=
  C t (unweightThresholdPathGlobal s0 p a t)

def weightedThresholdSelfTail
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (a : ThresholdWeightedPath s0 p) (s : ℝ) : ℝ × ℝ :=
  -(∫ t in Ioi s, weightedThresholdSelfSource C s0 p a t)

def thresholdSelfLipschitzConstant
    (s0 p nu Lc : ℝ) : ℝ :=
  Lc / (p + nu - 2) * s0 ^ (1 - nu)

theorem thresholdSelfLipschitzConstant_nonneg
    {s0 p nu Lc : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu) (hLc : 0 ≤ Lc) :
    0 ≤ thresholdSelfLipschitzConstant s0 p nu Lc := by
  unfold thresholdSelfLipschitzConstant
  positivity

theorem thresholdSelfLipschitzConstant_tendsto_zero
    (p nu Lc : ℝ) (hnu : 2 < nu) :
    Tendsto (fun s0 : ℝ => thresholdSelfLipschitzConstant s0 p nu Lc)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun s0 : ℝ => s0 ^ (1 - nu)) atTop (𝓝 0) := by
    have he : -(nu - 1) = 1 - nu := by ring
    simpa only [he] using tendsto_rpow_neg_atTop (show 0 < nu - 1 by linarith)
  unfold thresholdSelfLipschitzConstant
  simpa only [mul_zero] using hpow.const_mul (Lc / (p + nu - 2))

theorem weightedThresholdSelfSource_continuous
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0)
    (hC : Continuous C) (a : ThresholdWeightedPath s0 p) :
    Continuous (weightedThresholdSelfSource C s0 p a) := by
  exact hC.clm_apply (unweightThresholdPathGlobal_continuous s0 p hs0 a)

private theorem weightedThresholdSelfSource_bound
    {C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    {s0 p nu Lc t : ℝ}
    (hs0 : 0 < s0) (hLc : 0 ≤ Lc)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p) (ht : s0 ≤ t) :
    ‖weightedThresholdSelfSource C s0 p a t‖ ≤
      (Lc * ‖a‖) * t ^ (1 - p - nu) := by
  have htpos : 0 < t := hs0.trans_le ht
  have ha := unweightThresholdPathGlobal_norm_bound s0 p hs0 a ht
  calc
    ‖weightedThresholdSelfSource C s0 p a t‖
        ≤ ‖C t‖ * ‖unweightThresholdPathGlobal s0 p a t‖ :=
          (C t).le_opNorm _
    _ ≤ (Lc * t ^ (-nu)) * (‖a‖ * t ^ (1 - p)) :=
      mul_le_mul (hC t ht) ha (norm_nonneg _)
        (mul_nonneg hLc (Real.rpow_nonneg htpos.le _))
    _ = (Lc * ‖a‖) * t ^ (1 - p - nu) := by
      rw [← Real.rpow_add htpos]
      congr 1 <;> ring

theorem weightedThresholdSelfSource_integrable
    {s0 p nu Lc : ℝ}
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p)
    {s : ℝ} (hs : s0 ≤ s) :
    IntegrableOn (weightedThresholdSelfSource C s0 p a) (Ioi s) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hexp : 1 - p - nu < -1 := by linarith
  have hmajor : IntegrableOn
      (fun t : ℝ => (Lc * ‖a‖) * t ^ (1 - p - nu)) (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt hexp hsp).const_mul (Lc * ‖a‖)
  have hmeas :
      AEStronglyMeasurable (weightedThresholdSelfSource C s0 p a)
        (volume.restrict (Ioi s)) :=
    (weightedThresholdSelfSource_continuous C s0 p hs0 hCcont a)
      .aestronglyMeasurable.restrict
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact weightedThresholdSelfSource_bound hs0 hLc hC a (hs.trans ht.le)

theorem weightedThresholdSelfTail_bound
    {s0 p nu Lc : ℝ}
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p)
    {s : ℝ} (hs : s0 ≤ s) :
    ‖weightedThresholdSelfTail C s0 p a s‖ ≤
      (Lc * ‖a‖) / (p + nu - 2) * s ^ (2 - p - nu) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hi := weightedThresholdSelfSource_integrable
    C hs0 hp hnu hLc hCcont hC a hs
  have hpow : IntegrableOn (fun t : ℝ => t ^ (1 - p - nu)) (Ioi s) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hsp
  have hmajor := hpow.const_mul (Lc * ‖a‖)
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi s),
      ‖weightedThresholdSelfSource C s0 p a t‖ ≤
        (Lc * ‖a‖) * t ^ (1 - p - nu) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact weightedThresholdSelfSource_bound hs0 hLc hC a (hs.trans ht.le)
  have hI : (∫ t in Ioi s, t ^ (1 - p - nu)) =
      s ^ (2 - p - nu) / (p + nu - 2) := by
    have h1 : -1 - (p + nu - 2) = 1 - p - nu := by ring
    have h2 : -(p + nu - 2) = 2 - p - nu := by ring
    simpa only [h1,h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀ := s) (δ := p + nu - 2) hsp (by linarith))
  unfold weightedThresholdSelfTail
  rw [norm_neg]
  calc
    ‖∫ t in Ioi s, weightedThresholdSelfSource C s0 p a t‖
        ≤ ∫ t in Ioi s, (Lc * ‖a‖) * t ^ (1 - p - nu) :=
      norm_integral_le_of_norm_le hmajor hpoint
    _ = (Lc * ‖a‖) * (s ^ (2 - p - nu) / (p + nu - 2)) := by
      rw [integral_const_mul,hI]
    _ = (Lc * ‖a‖) / (p + nu - 2) * s ^ (2 - p - nu) := by ring

private theorem weightedThresholdSelfTail_eq_fixed
    {s0 p nu Lc : ℝ}
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p)
    {s : ℝ} (hs : s0 ≤ s) :
    weightedThresholdSelfTail C s0 p a s =
      -(∫ t in Ioi s0, weightedThresholdSelfSource C s0 p a t) +
        ∫ t in s0..s, weightedThresholdSelfSource C s0 p a t := by
  have hi := weightedThresholdSelfSource_integrable
    C hs0 hp hnu hLc hCcont hC a le_rfl
  have h := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi hs))
  unfold weightedThresholdSelfTail
  rw [← h]
  abel

theorem weightedThresholdSelfTail_continuousOn
    {s0 p nu Lc : ℝ}
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p) :
    ContinuousOn (weightedThresholdSelfTail C s0 p a) (Ici s0) := by
  have hsrc := weightedThresholdSelfSource_continuous C s0 p hs0 hCcont a
  have hi := weightedThresholdSelfSource_integrable
    C hs0 hp hnu hLc hCcont hC a le_rfl
  have hc : Continuous (fun s =>
      -(∫ t in Ioi s0, weightedThresholdSelfSource C s0 p a t) +
        ∫ t in s0..s, weightedThresholdSelfSource C s0 p a t) :=
    continuous_const.add
      (intervalIntegral.differentiable_integral_of_continuous hsrc).continuous
  apply hc.continuousOn.congr
  intro s hs
  exact (weightedThresholdSelfTail_eq_fixed
    C hs0 hp hnu hLc hCcont hC a hs).symm

def weightedThresholdSelfValue
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (a : ThresholdWeightedPath s0 p)
    (s : LateTime s0) : ℝ × ℝ :=
  ((s : ℝ) ^ (p - 1)) • weightedThresholdSelfTail C s0 p a s

theorem weightedThresholdSelfValue_continuous
    {s0 p nu Lc : ℝ}
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p) :
    Continuous (weightedThresholdSelfValue C s0 p a) := by
  have htail :
      Continuous (fun s : LateTime s0 => weightedThresholdSelfTail C s0 p a s) :=
    (weightedThresholdSelfTail_continuousOn
      C hs0 hp hnu hLc hCcont hC a).domRestrict
  apply continuous_iff_continuousAt.2
  intro s
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have hpow :
      ContinuousAt (fun t : LateTime s0 => ((t : ℝ) ^ (p - 1))) s := by
    exact (Real.continuousAt_rpow_const (s : ℝ) (p - 1)
      (Or.inl hspos.ne')).comp continuousAt_subtype_val
  exact hpow.smul htail.continuousAt

theorem weightedThresholdSelfValue_bound
    {s0 p nu Lc : ℝ}
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p) (s : LateTime s0) :
    ‖weightedThresholdSelfValue C s0 p a s‖ ≤
      thresholdSelfLipschitzConstant s0 p nu Lc * ‖a‖ := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have ht := weightedThresholdSelfTail_bound
    C hs0 hp hnu hLc hCcont hC a s.2
  unfold weightedThresholdSelfValue thresholdSelfLipschitzConstant
  rw [norm_smul,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hspos _)]
  have hpow :
      (s : ℝ) ^ (p - 1) * (s : ℝ) ^ (2 - p - nu) =
        (s : ℝ) ^ (1 - nu) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring
  have hmono :
      (s : ℝ) ^ (1 - nu) ≤ s0 ^ (1 - nu) :=
    Real.rpow_le_rpow_of_nonpos hs0 s.2 (by linarith)
  have hcoef :
      0 ≤ (Lc * ‖a‖) / (p + nu - 2) := by
    positivity
  calc
    (s : ℝ) ^ (p - 1) * ‖weightedThresholdSelfTail C s0 p a s‖
        ≤ (s : ℝ) ^ (p - 1) *
          ((Lc * ‖a‖) / (p + nu - 2) *
            (s : ℝ) ^ (2 - p - nu)) := by
          exact mul_le_mul_of_nonneg_left ht
            (Real.rpow_nonneg hspos.le _)
    _ = (Lc * ‖a‖) / (p + nu - 2) * (s : ℝ) ^ (1 - nu) := by
      rw [← hpow]
      ring
    _ ≤ (Lc * ‖a‖) / (p + nu - 2) * s0 ^ (1 - nu) :=
      mul_le_mul_of_nonneg_left hmono hcoef
    _ = Lc / (p + nu - 2) * s0 ^ (1 - nu) * ‖a‖ := by ring

def weightedThresholdSelfMap
    {s0 p nu Lc : ℝ}
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu)) :
    ThresholdWeightedPath s0 p → ThresholdWeightedPath s0 p :=
  fun a =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (weightedThresholdSelfValue C s0 p a)
      (weightedThresholdSelfValue_continuous
        C hs0 hp hnu hLc hCcont hC a)
      (thresholdSelfLipschitzConstant s0 p nu Lc * ‖a‖)
      (weightedThresholdSelfValue_bound
        C hs0 hp hnu hLc hCcont hC a)

private theorem weightedThresholdSelfSource_sub
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (a b : ThresholdWeightedPath s0 p) (t : ℝ) :
    weightedThresholdSelfSource C s0 p a t -
        weightedThresholdSelfSource C s0 p b t =
      weightedThresholdSelfSource C s0 p (a - b) t := by
  unfold weightedThresholdSelfSource unweightThresholdPathGlobal
    unweightPathGlobal
  rw [← map_sub]
  simp only [BoundedContinuousFunction.sub_apply, smul_sub]

theorem weightedThresholdSelfTail_sub
    {s0 p nu Lc : ℝ}
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a b : ThresholdWeightedPath s0 p)
    {s : ℝ} (hs : s0 ≤ s) :
    weightedThresholdSelfTail C s0 p a s -
        weightedThresholdSelfTail C s0 p b s =
      weightedThresholdSelfTail C s0 p (a - b) s := by
  have hia := weightedThresholdSelfSource_integrable
    C hs0 hp hnu hLc hCcont hC a hs
  have hib := weightedThresholdSelfSource_integrable
    C hs0 hp hnu hLc hCcont hC b hs
  unfold weightedThresholdSelfTail
  rw [sub_eq_add_neg, ← neg_add, ← integral_sub hia hib]
  congr 1
  funext t
  exact weightedThresholdSelfSource_sub C s0 p a b t

theorem weightedThresholdSelfMap_difference_norm
    {s0 p nu Lc : ℝ}
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a b : ThresholdWeightedPath s0 p) :
    ‖weightedThresholdSelfMap C hs0 hp hnu hLc hCcont hC a -
        weightedThresholdSelfMap C hs0 hp hnu hLc hCcont hC b‖ ≤
      thresholdSelfLipschitzConstant s0 p nu Lc * ‖a - b‖ := by
  have hnon :
      0 ≤ thresholdSelfLipschitzConstant s0 p nu Lc :=
    thresholdSelfLipschitzConstant_nonneg hs0 hp hnu hLc
  have hC0 : 0 ≤ thresholdSelfLipschitzConstant s0 p nu Lc * ‖a-b‖ :=
    mul_nonneg hnon (norm_nonneg _)
  rw [BoundedContinuousFunction.norm_le hC0]
  intro s
  change ‖weightedThresholdSelfValue C s0 p a s -
      weightedThresholdSelfValue C s0 p b s‖ ≤ _
  have hsub := weightedThresholdSelfTail_sub
    C hs0 hp hnu hLc hCcont hC a b s.2
  have hval :
      weightedThresholdSelfValue C s0 p a s -
          weightedThresholdSelfValue C s0 p b s =
        ((s : ℝ) ^ (p - 1)) •
          weightedThresholdSelfTail C s0 p (a-b) s := by
    unfold weightedThresholdSelfValue
    rw [← smul_sub,hsub]
  rw [hval]
  exact weightedThresholdSelfValue_bound
    C hs0 hp hnu hLc hCcont hC (a-b) s

theorem weightedThresholdSelfMap_lipschitz
    {s0 p nu Lc : ℝ}
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu)) :
    LipschitzWith
      (Real.toNNReal (thresholdSelfLipschitzConstant s0 p nu Lc))
      (weightedThresholdSelfMap C hs0 hp hnu hLc hCcont hC) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hnon :
      0 ≤ thresholdSelfLipschitzConstant s0 p nu Lc :=
    thresholdSelfLipschitzConstant_nonneg hs0 hp hnu hLc
  rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ hnon]
  exact weightedThresholdSelfMap_difference_norm
    C hs0 hp hnu hLc hCcont hC a b

#print axioms thresholdSelfLipschitzConstant_tendsto_zero
#print axioms weightedThresholdSelfTail_bound
#print axioms weightedThresholdSelfMap_difference_norm
#print axioms weightedThresholdSelfMap_lipschitz

end HBL.MainBackward
