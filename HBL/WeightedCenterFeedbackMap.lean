import HBL.WeightedBackwardPaths
import HBL.KinematicTailEstimates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Standard constrained centre propagator and its weighted feedback map

The propagator existence/strong continuity is the standard Kato--Kisyński
linear-evolution boundary.  It acts on the *actual* closed constrained Hartree
centre space constructed in ConstrainedCenterSpace.  All polynomial decay
and Lipschitz constants below are proved natively.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.MainBackward

/-- Standard nonautonomous propagator on the actual constrained centre space.
The Duhamel-continuity clause is a standard consequence of strong continuity;
it contains no HBL blow-up or shooting conclusion. -/
structure StandardConstrainedCenterPropagator (s0 : ℝ) where
  U : ℝ → ℝ → ConstrainedCenterSpace →L[ℝ] ConstrainedCenterSpace
  boundConst : ℝ
  bound_nonneg : 0 ≤ boundConst
  bound : ∀ s t, s0 ≤ s → s ≤ t → ‖U s t‖ ≤ boundConst
  orbit_continuous :
    ∀ s : ℝ, ∀ F : ℝ → ConstrainedCenterSpace,
      Continuous F → Continuous (fun t => U s t (F t))
  duhamel_continuous :
    ∀ F : ℝ → ConstrainedCenterSpace,
      Continuous F →
      (∀ s, s0 ≤ s →
        IntegrableOn (fun t => U s t (F t)) (Ioi s)) →
      ContinuousOn
        (fun s => -(∫ t in Ioi s, U s t (F t))) (Ici s0)

def weightedCenterFeedbackSource
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (p : ℝ) (a : ThresholdWeightedPath s0 p)
    (s t : ℝ) : ConstrainedCenterSpace :=
  CE.U s t (E t (unweightThresholdPathGlobal s0 p a t))

def weightedCenterFeedbackTail
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (p : ℝ) (a : ThresholdWeightedPath s0 p)
    (s : ℝ) : ConstrainedCenterSpace :=
  -(∫ t in Ioi s, weightedCenterFeedbackSource CE E p a s t)

theorem weightedCenterPrimitiveSource_continuous
    {s0 : ℝ} (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (p : ℝ) (hs0 : 0 < s0)
    (hE : Continuous E) (a : ThresholdWeightedPath s0 p) :
    Continuous (fun t => E t (unweightThresholdPathGlobal s0 p a t)) := by
  exact hE.clm_apply (unweightThresholdPathGlobal_continuous s0 p hs0 a)

private theorem weightedCenterPrimitiveSource_bound
    {s0 p nu L : ℝ}
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hL : 0 ≤ L)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p)
    {t : ℝ} (ht : s0 ≤ t) :
    ‖E t (unweightThresholdPathGlobal s0 p a t)‖ ≤
      (L * ‖a‖) * t ^ (1 - p - nu) := by
  have htpos : 0 < t := hs0.trans_le ht
  have ha := unweightThresholdPathGlobal_norm_bound s0 p hs0 a ht
  have hop := (E t).le_opNorm (unweightThresholdPathGlobal s0 p a t)
  have hmul :
      ‖E t‖ * ‖unweightThresholdPathGlobal s0 p a t‖ ≤
        (L * t ^ (-nu)) * (‖a‖ * t ^ (1 - p)) := by
    exact mul_le_mul (hE t ht) ha (norm_nonneg _)
      (mul_nonneg hL (Real.rpow_nonneg htpos.le _))
  have hpow : t ^ (-nu) * t ^ (1 - p) =
      t ^ (1 - p - nu) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  calc
    ‖E t (unweightThresholdPathGlobal s0 p a t)‖
        ≤ ‖E t‖ * ‖unweightThresholdPathGlobal s0 p a t‖ := hop
    _ ≤ (L * t ^ (-nu)) * (‖a‖ * t ^ (1 - p)) := hmul
    _ = (L * ‖a‖) * t ^ (1 - p - nu) := by
      rw [← hpow]
      ring

theorem weightedCenterFeedbackSource_integrable
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p)
    {s : ℝ} (hs : s0 ≤ s) :
    IntegrableOn (weightedCenterFeedbackSource CE E p a s) (Ioi s) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hexp : 1 - p - nu < -1 := by linarith
  have hmajor : IntegrableOn
      (fun t : ℝ => (CE.boundConst * L * ‖a‖) * t ^ (1 - p - nu))
      (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt hexp hsp).const_mul
      (CE.boundConst * L * ‖a‖)
  have hprim :
      Continuous (fun t => E t (unweightThresholdPathGlobal s0 p a t)) :=
    weightedCenterPrimitiveSource_continuous E p hs0 hEcont a
  have hmeas :
      AEStronglyMeasurable (weightedCenterFeedbackSource CE E p a s)
        (volume.restrict (Ioi s)) := by
    exact (CE.orbit_continuous s
      (fun t => E t (unweightThresholdPathGlobal s0 p a t)) hprim)
        .aestronglyMeasurable.restrict
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hsrc := weightedCenterPrimitiveSource_bound E hs0 hL hE a (hs.trans ht.le)
  have hU := (CE.U s t).le_opNorm
    (E t (unweightThresholdPathGlobal s0 p a t))
  calc
    ‖weightedCenterFeedbackSource CE E p a s t‖
        ≤ ‖CE.U s t‖ *
          ‖E t (unweightThresholdPathGlobal s0 p a t)‖ := hU
    _ ≤ CE.boundConst * ((L * ‖a‖) * t ^ (1 - p - nu)) := by
      exact mul_le_mul (CE.bound s t hs ht.le) hsrc (norm_nonneg _)
        CE.bound_nonneg
    _ = (CE.boundConst * L * ‖a‖) * t ^ (1 - p - nu) := by ring



theorem weightedCenterFeedbackTail_bound
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p)
    {s : ℝ} (hs : s0 ≤ s) :
    ‖weightedCenterFeedbackTail CE E p a s‖ ≤
      (CE.boundConst * L * ‖a‖) / (p + nu - 2) *
        s ^ (2 - p - nu) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hi := weightedCenterFeedbackSource_integrable
    CE E hs0 hp hnu hL hEcont hE a hs
  have hpow : IntegrableOn (fun t : ℝ => t ^ (1 - p - nu)) (Ioi s) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hsp
  have hmajor := hpow.const_mul (CE.boundConst * L * ‖a‖)
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi s),
      ‖weightedCenterFeedbackSource CE E p a s t‖ ≤
        (CE.boundConst * L * ‖a‖) * t ^ (1 - p - nu) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hsrc := weightedCenterPrimitiveSource_bound
      E hs0 hL hE a (hs.trans ht.le)
    have hU := (CE.U s t).le_opNorm
      (E t (unweightThresholdPathGlobal s0 p a t))
    calc
      ‖weightedCenterFeedbackSource CE E p a s t‖
          ≤ ‖CE.U s t‖ *
            ‖E t (unweightThresholdPathGlobal s0 p a t)‖ := hU
      _ ≤ CE.boundConst *
            ((L * ‖a‖) * t ^ (1 - p - nu)) := by
          exact mul_le_mul (CE.bound s t hs ht.le) hsrc
            (norm_nonneg _) CE.bound_nonneg
      _ = (CE.boundConst * L * ‖a‖) * t ^ (1 - p - nu) := by ring
  have hI : (∫ t in Ioi s, t ^ (1 - p - nu)) =
      s ^ (2 - p - nu) / (p + nu - 2) := by
    have h1 : -1 - (p + nu - 2) = 1 - p - nu := by ring
    have h2 : -(p + nu - 2) = 2 - p - nu := by ring
    simpa only [h1, h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀ := s) (δ := p + nu - 2) hsp (by linarith))
  unfold weightedCenterFeedbackTail
  rw [norm_neg]
  calc
    ‖∫ t in Ioi s, weightedCenterFeedbackSource CE E p a s t‖
        ≤ ∫ t in Ioi s,
            (CE.boundConst * L * ‖a‖) * t ^ (1 - p - nu) :=
          norm_integral_le_of_norm_le hmajor hpoint
    _ = (CE.boundConst * L * ‖a‖) *
          (s ^ (2 - p - nu) / (p + nu - 2)) := by
          rw [integral_const_mul, hI]
    _ = (CE.boundConst * L * ‖a‖) / (p + nu - 2) *
          s ^ (2 - p - nu) := by ring

theorem weightedCenterFeedbackTail_continuousOn
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p) :
    ContinuousOn (weightedCenterFeedbackTail CE E p a) (Ici s0) := by
  let F : ℝ → ConstrainedCenterSpace :=
    fun t => E t (unweightThresholdPathGlobal s0 p a t)
  have hF : Continuous F :=
    weightedCenterPrimitiveSource_continuous E p hs0 hEcont a
  have hInt : ∀ s, s0 ≤ s →
      IntegrableOn (fun t => CE.U s t (F t)) (Ioi s) := by
    intro s hs
    exact weightedCenterFeedbackSource_integrable
      CE E hs0 hp hnu hL hEcont hE a hs
  exact CE.duhamel_continuous F hF hInt

def weightedCenterFeedbackValue
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (p : ℝ) (a : ThresholdWeightedPath s0 p)
    (s : LateTime s0) : ConstrainedCenterSpace :=
  ((s : ℝ) ^ p) • weightedCenterFeedbackTail CE E p a s

theorem weightedCenterFeedbackValue_continuous
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p) :
    Continuous (weightedCenterFeedbackValue CE E p a) := by
  have htail :
      Continuous (fun s : LateTime s0 =>
        weightedCenterFeedbackTail CE E p a s) :=
    (weightedCenterFeedbackTail_continuousOn
      CE E hs0 hp hnu hL hEcont hE a).domRestrict
  apply continuous_iff_continuousAt.2
  intro s
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have hpow :
      ContinuousAt (fun t : LateTime s0 => ((t : ℝ) ^ p)) s := by
    exact (Real.continuousAt_rpow_const (s : ℝ) p
      (Or.inl hspos.ne')).comp continuousAt_subtype_val
  exact hpow.smul htail.continuousAt

def centerFeedbackLipschitzConstant
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (p nu L : ℝ) : ℝ :=
  (CE.boundConst * L) / (p + nu - 2) * s0 ^ (2 - nu)

theorem centerFeedbackLipschitzConstant_nonneg
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu) (hL : 0 ≤ L) :
    0 ≤ centerFeedbackLipschitzConstant CE p nu L := by
  unfold centerFeedbackLipschitzConstant
  positivity

theorem weightedCenterFeedbackValue_bound
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p) (s : LateTime s0) :
    ‖weightedCenterFeedbackValue CE E p a s‖ ≤
      centerFeedbackLipschitzConstant CE p nu L * ‖a‖ := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have ht := weightedCenterFeedbackTail_bound
    CE E hs0 hp hnu hL hEcont hE a s.2
  unfold weightedCenterFeedbackValue
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hspos _)]
  have hpow :
      (s : ℝ) ^ p * (s : ℝ) ^ (2 - p - nu) =
        (s : ℝ) ^ (2 - nu) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring
  have hmono :
      (s : ℝ) ^ (2 - nu) ≤ s0 ^ (2 - nu) :=
    Real.rpow_le_rpow_of_nonpos hs0 s.2 (by linarith)
  have hcoef :
      0 ≤ (CE.boundConst * L * ‖a‖) / (p + nu - 2) := by
    positivity
  calc
    (s : ℝ) ^ p * ‖weightedCenterFeedbackTail CE E p a s‖
        ≤ (s : ℝ) ^ p *
          ((CE.boundConst * L * ‖a‖) / (p + nu - 2) *
            (s : ℝ) ^ (2 - p - nu)) := by
          exact mul_le_mul_of_nonneg_left ht
            (Real.rpow_nonneg hspos.le _)
    _ = (CE.boundConst * L * ‖a‖) / (p + nu - 2) *
          (s : ℝ) ^ (2 - nu) := by rw [← hpow]; ring
    _ ≤ (CE.boundConst * L * ‖a‖) / (p + nu - 2) *
          s0 ^ (2 - nu) :=
        mul_le_mul_of_nonneg_left hmono hcoef
    _ = centerFeedbackLipschitzConstant CE p nu L * ‖a‖ := by
      unfold centerFeedbackLipschitzConstant
      ring

def weightedCenterFeedbackMap
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu)) :
    ThresholdWeightedPath s0 p → CenterWeightedPath s0 p :=
  fun a =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (weightedCenterFeedbackValue CE E p a)
      (weightedCenterFeedbackValue_continuous
        CE E hs0 hp hnu hL hEcont hE a)
      (centerFeedbackLipschitzConstant CE p nu L * ‖a‖)
      (weightedCenterFeedbackValue_bound
        CE E hs0 hp hnu hL hEcont hE a)

private theorem weightedCenterFeedbackSource_sub
    {s0 : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (p : ℝ) (a b : ThresholdWeightedPath s0 p)
    (s t : ℝ) :
    weightedCenterFeedbackSource CE E p a s t -
        weightedCenterFeedbackSource CE E p b s t =
      weightedCenterFeedbackSource CE E p (a - b) s t := by
  unfold weightedCenterFeedbackSource unweightThresholdPathGlobal
    unweightPathGlobal
  rw [← map_sub, ← map_sub]
  simp only [BoundedContinuousFunction.sub_apply, smul_sub]

theorem weightedCenterFeedbackTail_sub
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (a b : ThresholdWeightedPath s0 p)
    {s : ℝ} (hs : s0 ≤ s) :
    weightedCenterFeedbackTail CE E p a s -
        weightedCenterFeedbackTail CE E p b s =
      weightedCenterFeedbackTail CE E p (a - b) s := by
  have hia := weightedCenterFeedbackSource_integrable
    CE E hs0 hp hnu hL hEcont hE a hs
  have hib := weightedCenterFeedbackSource_integrable
    CE E hs0 hp hnu hL hEcont hE b hs
  unfold weightedCenterFeedbackTail
  rw [sub_eq_add_neg, ← neg_add]
  rw [← integral_sub hia hib]
  congr 1
  funext t
  exact weightedCenterFeedbackSource_sub CE E p a b s t

theorem weightedCenterFeedbackMap_difference_norm
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (a b : ThresholdWeightedPath s0 p) :
    ‖weightedCenterFeedbackMap CE E hs0 hp hnu hL hEcont hE a -
        weightedCenterFeedbackMap CE E hs0 hp hnu hL hEcont hE b‖ ≤
      centerFeedbackLipschitzConstant CE p nu L * ‖a - b‖ := by
  have hC :
      0 ≤ centerFeedbackLipschitzConstant CE p nu L * ‖a - b‖ :=
    mul_nonneg
      (centerFeedbackLipschitzConstant_nonneg CE hs0 hp hnu hL)
      (norm_nonneg _)
  rw [BoundedContinuousFunction.norm_le hC]
  intro s
  change ‖weightedCenterFeedbackValue CE E p a s -
      weightedCenterFeedbackValue CE E p b s‖ ≤ _
  have hsub := weightedCenterFeedbackTail_sub
    CE E hs0 hp hnu hL hEcont hE a b s.2
  have hval :
      weightedCenterFeedbackValue CE E p a s -
          weightedCenterFeedbackValue CE E p b s =
        ((s : ℝ) ^ p) •
          weightedCenterFeedbackTail CE E p (a - b) s := by
    unfold weightedCenterFeedbackValue
    rw [← smul_sub, hsub]
  rw [hval]
  exact weightedCenterFeedbackValue_bound
    CE E hs0 hp hnu hL hEcont hE (a - b) s

theorem weightedCenterFeedbackMap_lipschitz
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu)) :
    LipschitzWith
      (Real.toNNReal (centerFeedbackLipschitzConstant CE p nu L))
      (weightedCenterFeedbackMap CE E hs0 hp hnu hL hEcont hE) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hnon :
      0 ≤ centerFeedbackLipschitzConstant CE p nu L :=
    centerFeedbackLipschitzConstant_nonneg CE hs0 hp hnu hL
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hnon]
  exact weightedCenterFeedbackMap_difference_norm
    CE E hs0 hp hnu hL hEcont hE a b

#print axioms weightedCenterFeedbackTail_bound
#print axioms weightedCenterFeedbackValue_bound
#print axioms weightedCenterFeedbackMap_difference_norm
#print axioms weightedCenterFeedbackMap_lipschitz

end HBL.MainBackward
