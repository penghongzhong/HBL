import HBL.WeightedCenterFeedbackMap
import HBL.WeightedCenterNonlinearMap
import Mathlib.Tactic

/-!
# Threshold feedback from a Lipschitz residual difference

For the final single-orbit Type-II construction we do not need to identify
the threshold-to-centre feedback with a Frechet derivative of the finite
profile residual.  It is enough to control the ACTUAL residual difference
directly:
  ||H(t,theta)-H(t,eta)|| <= L t^{-nu} ||theta-eta||, nu>2.

This module builds the same weighted Duhamel feedback map from that difference
estimate.  The polynomial time loss and contraction constant are exactly the
same as in the older linear-operator formulation.

This is the replacement interface for the final main chain; it is intended
to bypass residual-tangent differentiation and the associated long Kummer
parameter-derivative chain.  It does not assert the physical residual
Lipschitz bound itself.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.MainBackward

def weightedThresholdResidualFeedbackSource
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (p : ℝ) (a : ThresholdWeightedPath s0 p)
    (s t : ℝ) : ConstrainedCenterSpace :=
  CE.U s t (H t (unweightThresholdPathGlobal s0 p a t))

def weightedThresholdResidualFeedbackTail
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (p : ℝ) (a : ThresholdWeightedPath s0 p)
    (s : ℝ) : ConstrainedCenterSpace :=
  -(∫ t in Ioi s, weightedThresholdResidualFeedbackSource CE H p a s t)

private theorem thresholdResidualPrimitive_continuous
    {s0 p : ℝ}
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (hs0 : 0 < s0)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (a : ThresholdWeightedPath s0 p) :
    Continuous (fun t =>
      H t (unweightThresholdPathGlobal s0 p a t)) := by
  exact hHcont.comp
    (continuous_id.prodMk
      (unweightThresholdPathGlobal_continuous s0 p hs0 a))

private theorem thresholdResidualPrimitive_bound
    {s0 p nu L t : ℝ}
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hL : 0 ≤ L)
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖)
    (a : ThresholdWeightedPath s0 p)
    (ht : s0 ≤ t) :
    ‖H t (unweightThresholdPathGlobal s0 p a t)‖ ≤
      (L * ‖a‖) * t ^ (1 - p - nu) := by
  have htpos : 0 < t := hs0.trans_le ht
  have ha :=
    unweightThresholdPathGlobal_norm_bound s0 p hs0 a ht
  have hraw :=
    hHlip t ht (unweightThresholdPathGlobal s0 p a t) 0
  rw [hHzero t ht, sub_zero, sub_zero] at hraw
  have hcoef : 0 ≤ L * t ^ (-nu) :=
    mul_nonneg hL (Real.rpow_nonneg htpos.le _)
  have hmul :
      L * t ^ (-nu) *
          ‖unweightThresholdPathGlobal s0 p a t‖ ≤
        L * t ^ (-nu) * (‖a‖ * t ^ (1 - p)) :=
    mul_le_mul_of_nonneg_left ha hcoef
  have hpw :
      t ^ (-nu) * t ^ (1 - p) =
        t ^ (1 - p - nu) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  calc
    ‖H t (unweightThresholdPathGlobal s0 p a t)‖
        ≤ L * t ^ (-nu) *
          ‖unweightThresholdPathGlobal s0 p a t‖ := hraw
    _ ≤ L * t ^ (-nu) * (‖a‖ * t ^ (1 - p)) := hmul
    _ = (L * ‖a‖) * t ^ (1 - p - nu) := by
      rw [← hpw]
      ring

theorem weightedThresholdResidualFeedbackSource_integrable
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖)
    (a : ThresholdWeightedPath s0 p)
    {s : ℝ} (hs : s0 ≤ s) :
    IntegrableOn
      (weightedThresholdResidualFeedbackSource CE H p a s)
      (Ioi s) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hexp : 1 - p - nu < -1 := by linarith
  have hmajor : IntegrableOn
      (fun t : ℝ => (CE.boundConst * L * ‖a‖) *
        t ^ (1 - p - nu)) (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt hexp hsp).const_mul
      (CE.boundConst * L * ‖a‖)
  have hprim :=
    thresholdResidualPrimitive_continuous H hs0 hHcont a
  have hmeas :
      AEStronglyMeasurable
        (weightedThresholdResidualFeedbackSource CE H p a s)
        (volume.restrict (Ioi s)) :=
    (CE.orbit_continuous s _ hprim).aestronglyMeasurable.restrict
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hH :=
    thresholdResidualPrimitive_bound
      H hs0 hL hHzero hHlip a (hs.trans ht.le)
  calc
    ‖weightedThresholdResidualFeedbackSource CE H p a s t‖
        ≤ ‖CE.U s t‖ *
          ‖H t (unweightThresholdPathGlobal s0 p a t)‖ :=
      (CE.U s t).le_opNorm _
    _ ≤ CE.boundConst *
        ((L * ‖a‖) * t ^ (1 - p - nu)) := by
      exact mul_le_mul (CE.bound s t hs ht.le) hH
        (norm_nonneg _) CE.bound_nonneg
    _ = (CE.boundConst * L * ‖a‖) *
        t ^ (1 - p - nu) := by ring

theorem weightedThresholdResidualFeedbackTail_bound
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖)
    (a : ThresholdWeightedPath s0 p)
    {s : ℝ} (hs : s0 ≤ s) :
    ‖weightedThresholdResidualFeedbackTail CE H p a s‖ ≤
      (CE.boundConst * L * ‖a‖) / (p + nu - 2) *
        s ^ (2 - p - nu) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hi :=
    weightedThresholdResidualFeedbackSource_integrable
      CE H hs0 hp hnu hL hHcont hHzero hHlip a hs
  have hpow : IntegrableOn
      (fun t : ℝ => t ^ (1 - p - nu)) (Ioi s) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hsp
  have hmajor :=
    hpow.const_mul (CE.boundConst * L * ‖a‖)
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi s),
      ‖weightedThresholdResidualFeedbackSource CE H p a s t‖ ≤
        (CE.boundConst * L * ‖a‖) *
          t ^ (1 - p - nu) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hH :=
      thresholdResidualPrimitive_bound
        H hs0 hL hHzero hHlip a (hs.trans ht.le)
    calc
      ‖weightedThresholdResidualFeedbackSource CE H p a s t‖
          ≤ ‖CE.U s t‖ *
            ‖H t (unweightThresholdPathGlobal s0 p a t)‖ :=
        (CE.U s t).le_opNorm _
      _ ≤ CE.boundConst *
          ((L * ‖a‖) * t ^ (1 - p - nu)) := by
        exact mul_le_mul (CE.bound s t hs ht.le) hH
          (norm_nonneg _) CE.bound_nonneg
      _ = (CE.boundConst * L * ‖a‖) *
          t ^ (1 - p - nu) := by ring
  have hI :
      (∫ t in Ioi s, t ^ (1 - p - nu)) =
        s ^ (2 - p - nu) / (p + nu - 2) := by
    have h1 : -1 - (p + nu - 2) = 1 - p - nu := by ring
    have h2 : -(p + nu - 2) = 2 - p - nu := by ring
    simpa only [h1, h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀ := s) (δ := p + nu - 2) hsp (by linarith))
  unfold weightedThresholdResidualFeedbackTail
  rw [norm_neg]
  calc
    ‖∫ t in Ioi s,
        weightedThresholdResidualFeedbackSource CE H p a s t‖
        ≤ ∫ t in Ioi s,
          (CE.boundConst * L * ‖a‖) *
            t ^ (1 - p - nu) :=
      norm_integral_le_of_norm_le hmajor hpoint
    _ = (CE.boundConst * L * ‖a‖) *
        (s ^ (2 - p - nu) / (p + nu - 2)) := by
      rw [integral_const_mul, hI]
    _ = (CE.boundConst * L * ‖a‖) / (p + nu - 2) *
        s ^ (2 - p - nu) := by ring

theorem weightedThresholdResidualFeedbackTail_continuousOn
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖)
    (a : ThresholdWeightedPath s0 p) :
    ContinuousOn
      (weightedThresholdResidualFeedbackTail CE H p a) (Ici s0) := by
  let F : ℝ → ConstrainedCenterSpace :=
    fun t => H t (unweightThresholdPathGlobal s0 p a t)
  have hF : Continuous F :=
    thresholdResidualPrimitive_continuous H hs0 hHcont a
  have hInt : ∀ s, s0 ≤ s →
      IntegrableOn (fun t => CE.U s t (F t)) (Ioi s) := by
    intro s hs
    exact weightedThresholdResidualFeedbackSource_integrable
      CE H hs0 hp hnu hL hHcont hHzero hHlip a hs
  exact CE.duhamel_continuous F hF hInt

def weightedThresholdResidualFeedbackValue
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (p : ℝ) (a : ThresholdWeightedPath s0 p)
    (s : LateTime s0) : ConstrainedCenterSpace :=
  ((s : ℝ) ^ p) •
    weightedThresholdResidualFeedbackTail CE H p a s

theorem weightedThresholdResidualFeedbackValue_continuous
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖)
    (a : ThresholdWeightedPath s0 p) :
    Continuous
      (weightedThresholdResidualFeedbackValue CE H p a) := by
  have htail :
      Continuous (fun s : LateTime s0 =>
        weightedThresholdResidualFeedbackTail CE H p a s) :=
    (weightedThresholdResidualFeedbackTail_continuousOn
      CE H hs0 hp hnu hL hHcont hHzero hHlip a).domRestrict
  apply continuous_iff_continuousAt.2
  intro s
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have hpw :
      ContinuousAt (fun t : LateTime s0 => (t : ℝ) ^ p) s := by
    exact (Real.continuousAt_rpow_const (s : ℝ) p
      (Or.inl hspos.ne')).comp continuousAt_subtype_val
  exact hpw.smul htail.continuousAt

theorem weightedThresholdResidualFeedbackValue_bound
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖)
    (a : ThresholdWeightedPath s0 p)
    (s : LateTime s0) :
    ‖weightedThresholdResidualFeedbackValue CE H p a s‖ ≤
      centerFeedbackLipschitzConstant CE p nu L * ‖a‖ := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have ht :=
    weightedThresholdResidualFeedbackTail_bound
      CE H hs0 hp hnu hL hHcont hHzero hHlip a s.2
  unfold weightedThresholdResidualFeedbackValue
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
  have hden : 0 < p + nu - 2 := by linarith
  have hnum : 0 ≤ CE.boundConst * L * ‖a‖ :=
    mul_nonneg (mul_nonneg CE.bound_nonneg hL) (norm_nonneg _)
  have hc :
      0 ≤ (CE.boundConst * L * ‖a‖) / (p + nu - 2) :=
    div_nonneg hnum hden.le
  calc
    (s : ℝ) ^ p *
      ‖weightedThresholdResidualFeedbackTail CE H p a s‖
        ≤ (s : ℝ) ^ p *
          ((CE.boundConst * L * ‖a‖) / (p + nu - 2) *
            (s : ℝ) ^ (2 - p - nu)) :=
      mul_le_mul_of_nonneg_left ht
        (Real.rpow_nonneg hspos.le _)
    _ = (CE.boundConst * L * ‖a‖) / (p + nu - 2) *
        (s : ℝ) ^ (2 - nu) := by
      rw [← hpow]
      ring
    _ ≤ (CE.boundConst * L * ‖a‖) / (p + nu - 2) *
        s0 ^ (2 - nu) :=
      mul_le_mul_of_nonneg_left hmono hc
    _ = centerFeedbackLipschitzConstant CE p nu L * ‖a‖ := by
      unfold centerFeedbackLipschitzConstant
      ring

def weightedThresholdResidualFeedbackMap
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖) :
    ThresholdWeightedPath s0 p → CenterWeightedPath s0 p :=
  fun a =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (weightedThresholdResidualFeedbackValue CE H p a)
      (weightedThresholdResidualFeedbackValue_continuous
        CE H hs0 hp hnu hL hHcont hHzero hHlip a)
      (centerFeedbackLipschitzConstant CE p nu L * ‖a‖)
      (weightedThresholdResidualFeedbackValue_bound
        CE H hs0 hp hnu hL hHcont hHzero hHlip a)

theorem weightedThresholdResidualFeedbackMap_difference_norm
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖)
    (a b : ThresholdWeightedPath s0 p) :
    ‖weightedThresholdResidualFeedbackMap
        CE H hs0 hp hnu hL hHcont hHzero hHlip a -
      weightedThresholdResidualFeedbackMap
        CE H hs0 hp hnu hL hHcont hHzero hHlip b‖ ≤
      centerFeedbackLipschitzConstant CE p nu L * ‖a - b‖ := by
  have hC :
      0 ≤ centerFeedbackLipschitzConstant CE p nu L * ‖a - b‖ :=
    mul_nonneg
      (centerFeedbackLipschitzConstant_nonneg
        CE hs0 hp hnu hL)
      (norm_nonneg _)
  rw [BoundedContinuousFunction.norm_le hC]
  intro s
  change
    ‖weightedThresholdResidualFeedbackValue CE H p a s -
      weightedThresholdResidualFeedbackValue CE H p b s‖ ≤ _
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have hia :=
    weightedThresholdResidualFeedbackSource_integrable
      CE H hs0 hp hnu hL hHcont hHzero hHlip a s.2
  have hib :=
    weightedThresholdResidualFeedbackSource_integrable
      CE H hs0 hp hnu hL hHcont hHzero hHlip b s.2
  have hdiff (t : ℝ) (ht : (s : ℝ) ≤ t) :
      ‖H t (unweightThresholdPathGlobal s0 p a t) -
        H t (unweightThresholdPathGlobal s0 p b t)‖ ≤
      (L * ‖a-b‖) * t ^ (1 - p - nu) := by
    have ht0 : s0 ≤ t := s.2.trans ht
    have hab :=
      unweightThresholdPathGlobal_difference_bound
        s0 p hs0 a b ht0
    have hraw :=
      hHlip t ht0
        (unweightThresholdPathGlobal s0 p a t)
        (unweightThresholdPathGlobal s0 p b t)
    have htpos : 0 < t := hs0.trans_le ht0
    have hcoef : 0 ≤ L * t ^ (-nu) :=
      mul_nonneg hL (Real.rpow_nonneg htpos.le _)
    have hmul :
        L * t ^ (-nu) *
            ‖unweightThresholdPathGlobal s0 p a t -
              unweightThresholdPathGlobal s0 p b t‖ ≤
          L * t ^ (-nu) * (‖a-b‖ * t ^ (1-p)) :=
      mul_le_mul_of_nonneg_left hab hcoef
    have hpw :
        t ^ (-nu) * t ^ (1-p) =
          t ^ (1-p-nu) := by
      rw [← Real.rpow_add htpos]
      congr 1
      ring
    calc
      _ ≤ L * t ^ (-nu) *
          ‖unweightThresholdPathGlobal s0 p a t -
            unweightThresholdPathGlobal s0 p b t‖ := hraw
      _ ≤ L * t ^ (-nu) * (‖a-b‖ * t ^ (1-p)) := hmul
      _ = (L * ‖a-b‖) * t ^ (1-p-nu) := by
        rw [← hpw]
        ring
  have hmajor : IntegrableOn
      (fun t : ℝ => (CE.boundConst * L * ‖a-b‖) *
        t ^ (1-p-nu)) (Ioi (s : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hspos).const_mul _
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi (s : ℝ)),
      ‖CE.U s t
        (H t (unweightThresholdPathGlobal s0 p a t) -
          H t (unweightThresholdPathGlobal s0 p b t))‖ ≤
      (CE.boundConst * L * ‖a-b‖) *
        t ^ (1-p-nu) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      _ ≤ ‖CE.U s t‖ *
          ‖H t (unweightThresholdPathGlobal s0 p a t) -
            H t (unweightThresholdPathGlobal s0 p b t)‖ :=
        (CE.U s t).le_opNorm _
      _ ≤ CE.boundConst *
          ((L * ‖a-b‖) * t ^ (1-p-nu)) := by
        exact mul_le_mul (CE.bound s t s.2 ht.le)
          (hdiff t ht.le) (norm_nonneg _) CE.bound_nonneg
      _ = (CE.boundConst * L * ‖a-b‖) *
          t ^ (1-p-nu) := by ring
  have hInt :
      (∫ t in Ioi (s : ℝ),
          weightedThresholdResidualFeedbackSource CE H p a s t) -
        (∫ t in Ioi (s : ℝ),
          weightedThresholdResidualFeedbackSource CE H p b s t) =
      ∫ t in Ioi (s : ℝ),
        CE.U s t
          (H t (unweightThresholdPathGlobal s0 p a t) -
            H t (unweightThresholdPathGlobal s0 p b t)) := by
    calc
      _ = ∫ t in Ioi (s : ℝ),
          (weightedThresholdResidualFeedbackSource CE H p a s t -
            weightedThresholdResidualFeedbackSource CE H p b s t) := by
          symm
          exact integral_sub hia hib
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with t
        unfold weightedThresholdResidualFeedbackSource
        rw [map_sub]
  have htailEq :
      weightedThresholdResidualFeedbackTail CE H p a s -
        weightedThresholdResidualFeedbackTail CE H p b s =
      -((∫ t in Ioi (s : ℝ),
          weightedThresholdResidualFeedbackSource CE H p a s t) -
        (∫ t in Ioi (s : ℝ),
          weightedThresholdResidualFeedbackSource CE H p b s t)) := by
    unfold weightedThresholdResidualFeedbackTail
    abel
  have htail :
      ‖weightedThresholdResidualFeedbackTail CE H p a s -
        weightedThresholdResidualFeedbackTail CE H p b s‖ ≤
      (CE.boundConst * L * ‖a-b‖) / (p+nu-2) *
        (s : ℝ) ^ (2-p-nu) := by
    rw [htailEq, norm_neg, hInt]
    have hI :
        (∫ t in Ioi (s : ℝ), t ^ (1-p-nu)) =
          (s : ℝ) ^ (2-p-nu) / (p+nu-2) := by
      have h1 : -1-(p+nu-2) = 1-p-nu := by ring
      have h2 : -(p+nu-2) = 2-p-nu := by ring
      simpa only [h1,h2] using
        (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
          (s₀ := (s : ℝ)) (δ := p+nu-2)
          hspos (by linarith))
    calc
      ‖∫ t in Ioi (s : ℝ),
          CE.U s t
            (H t (unweightThresholdPathGlobal s0 p a t) -
              H t (unweightThresholdPathGlobal s0 p b t))‖
        ≤ ∫ t in Ioi (s : ℝ),
          (CE.boundConst * L * ‖a-b‖) *
            t ^ (1-p-nu) :=
          norm_integral_le_of_norm_le hmajor hpoint
      _ = (CE.boundConst * L * ‖a-b‖) *
          ((s : ℝ) ^ (2-p-nu) / (p+nu-2)) := by
        rw [integral_const_mul,hI]
      _ = _ := by ring
  have hvalEq :
      weightedThresholdResidualFeedbackValue CE H p a s -
        weightedThresholdResidualFeedbackValue CE H p b s =
      ((s : ℝ) ^ p) •
        (weightedThresholdResidualFeedbackTail CE H p a s -
          weightedThresholdResidualFeedbackTail CE H p b s) := by
    unfold weightedThresholdResidualFeedbackValue
    exact (smul_sub _ _ _).symm
  rw [hvalEq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hspos _)]
  have hpw :
      (s : ℝ)^p * (s : ℝ)^(2-p-nu) =
        (s : ℝ)^(2-nu) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring
  have hmono :
      (s : ℝ)^(2-nu) ≤ s0^(2-nu) :=
    Real.rpow_le_rpow_of_nonpos hs0 s.2 (by linarith)
  have hden : 0 < p+nu-2 := by linarith
  have hnum : 0 ≤ CE.boundConst * L * ‖a-b‖ :=
    mul_nonneg (mul_nonneg CE.bound_nonneg hL) (norm_nonneg _)
  have hc :
      0 ≤ (CE.boundConst * L * ‖a-b‖)/(p+nu-2) :=
    div_nonneg hnum hden.le
  calc
    (s : ℝ)^p *
        ‖weightedThresholdResidualFeedbackTail CE H p a s -
          weightedThresholdResidualFeedbackTail CE H p b s‖
      ≤ (s : ℝ)^p *
          ((CE.boundConst * L * ‖a-b‖)/(p+nu-2) *
            (s : ℝ)^(2-p-nu)) :=
        mul_le_mul_of_nonneg_left htail
          (Real.rpow_nonneg hspos.le _)
    _ = (CE.boundConst * L * ‖a-b‖)/(p+nu-2) *
        (s : ℝ)^(2-nu) := by
      rw [← hpw]
      ring
    _ ≤ (CE.boundConst * L * ‖a-b‖)/(p+nu-2) *
        s0^(2-nu) :=
      mul_le_mul_of_nonneg_left hmono hc
    _ = centerFeedbackLipschitzConstant CE p nu L * ‖a-b‖ := by
      unfold centerFeedbackLipschitzConstant
      ring

theorem weightedThresholdResidualFeedbackMap_lipschitz
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖) :
    LipschitzWith
      (Real.toNNReal (centerFeedbackLipschitzConstant CE p nu L))
      (weightedThresholdResidualFeedbackMap
        CE H hs0 hp hnu hL hHcont hHzero hHlip) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hnon :
      0 ≤ centerFeedbackLipschitzConstant CE p nu L :=
    centerFeedbackLipschitzConstant_nonneg
      CE hs0 hp hnu hL
  rw [Real.coe_toNNReal _ hnon]
  have hout :=
    centerWeightedPath_dist_eq_norm_sub s0 p
      (weightedThresholdResidualFeedbackMap
        CE H hs0 hp hnu hL hHcont hHzero hHlip a)
      (weightedThresholdResidualFeedbackMap
        CE H hs0 hp hnu hL hHcont hHzero hHlip b)
  have hin : dist a b = ‖a-b‖ := by
    rw [BoundedContinuousFunction.dist_eq_iSup,
      BoundedContinuousFunction.norm_eq_iSup_norm]
    simp only [BoundedContinuousFunction.sub_apply, dist_eq_norm_sub]
  rw [hout, hin]
  exact weightedThresholdResidualFeedbackMap_difference_norm
    CE H hs0 hp hnu hL hHcont hHzero hHlip a b

end HBL.MainBackward
