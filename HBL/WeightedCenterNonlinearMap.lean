import HBL.WeightedCenterFeedbackMap
import Mathlib.Tactic

/-!
# Weighted nonlinear constrained-centre map

This is the genuine nonlinear half of the repaired HBL centre fixed point.
The source is evaluated on the actual constrained weighted centre path.
The only analytic input is the standard localized Hartree Lipschitz estimate
with one integrable time gain.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.MainBackward

def weightedCenterNonlinearSource
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (p : ℝ) (q : CenterWeightedPath s0 p)
    (s t : ℝ) : ConstrainedCenterSpace :=
  CE.U s t (G t (unweightPathGlobal p s0 q t))

def weightedCenterNonlinearTail
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (p : ℝ) (q : CenterWeightedPath s0 p)
    (s : ℝ) : ConstrainedCenterSpace :=
  -(∫ t in Ioi s, weightedCenterNonlinearSource CE G p q s t)

def centerNonlinearLipschitzConstant
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (p delta Cnl : ℝ) : ℝ :=
  (CE.boundConst * Cnl) / (p + delta) * s0 ^ (-delta)

theorem centerNonlinearLipschitzConstant_nonneg
    {s0 p delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCnl : 0 ≤ Cnl) :
    0 ≤ centerNonlinearLipschitzConstant CE p delta Cnl := by
  unfold centerNonlinearLipschitzConstant
  have hden : 0 < p + delta := by linarith
  have hnum : 0 ≤ CE.boundConst * Cnl :=
    mul_nonneg CE.bound_nonneg hCnl
  exact mul_nonneg (div_nonneg hnum hden.le)
    (Real.rpow_nonneg hs0.le _)

private theorem nonlinearPrimitive_continuous
    {s0 p : ℝ}
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (q : CenterWeightedPath s0 p) :
    Continuous (fun t => G t (unweightPathGlobal p s0 q t)) := by
  exact hGcont.comp
    (continuous_id.prodMk (unweightPathGlobal_continuous p s0 hs0 q))

private theorem nonlinearPrimitive_bound
    {s0 p delta Cnl t : ℝ}
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hCnl : 0 ≤ Cnl)
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q : CenterWeightedPath s0 p) (ht : s0 ≤ t) :
    ‖G t (unweightPathGlobal p s0 q t)‖ ≤
      (Cnl * ‖q‖) * t ^ (-p - 1 - delta) := by
  have htpos : 0 < t := hs0.trans_le ht
  have hq := unweightPathGlobal_norm_bound p s0 hs0 q ht
  have h := hGlip t ht (unweightPathGlobal p s0 q t) 0
  rw [hGzero t ht, sub_zero, sub_zero] at h
  have hmul :
      Cnl * t ^ (-1 - delta) * ‖unweightPathGlobal p s0 q t‖ ≤
        Cnl * t ^ (-1 - delta) * (‖q‖ * t ^ (-p)) := by
    exact mul_le_mul_of_nonneg_left hq
      (mul_nonneg hCnl (Real.rpow_nonneg htpos.le _))
  have hpw :
      t ^ (-1 - delta) * t ^ (-p) = t ^ (-p - 1 - delta) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  calc
    ‖G t (unweightPathGlobal p s0 q t)‖
        ≤ Cnl * t ^ (-1 - delta) *
          ‖unweightPathGlobal p s0 q t‖ := h
    _ ≤ Cnl * t ^ (-1 - delta) * (‖q‖ * t ^ (-p)) := hmul
    _ = (Cnl * ‖q‖) * t ^ (-p - 1 - delta) := by
      rw [← hpw]
      ring

theorem weightedCenterNonlinearSource_integrable
    {s0 p delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q : CenterWeightedPath s0 p) {s : ℝ} (hs : s0 ≤ s) :
    IntegrableOn (weightedCenterNonlinearSource CE G p q s) (Ioi s) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hexp : -p - 1 - delta < -1 := by linarith
  have hmajor : IntegrableOn
      (fun t : ℝ => (CE.boundConst * Cnl * ‖q‖) * t ^ (-p - 1 - delta))
      (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt hexp hsp).const_mul
      (CE.boundConst * Cnl * ‖q‖)
  have hprim := nonlinearPrimitive_continuous G hs0 hGcont q
  have hmeas :
      AEStronglyMeasurable (weightedCenterNonlinearSource CE G p q s)
        (volume.restrict (Ioi s)) :=
    (CE.orbit_continuous s _ hprim).aestronglyMeasurable.restrict
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hg := nonlinearPrimitive_bound G hs0 hCnl hGzero hGlip q (hs.trans ht.le)
  calc
    ‖weightedCenterNonlinearSource CE G p q s t‖
        ≤ ‖CE.U s t‖ * ‖G t (unweightPathGlobal p s0 q t)‖ :=
          (CE.U s t).le_opNorm _
    _ ≤ CE.boundConst * ((Cnl * ‖q‖) * t ^ (-p - 1 - delta)) := by
      exact mul_le_mul (CE.bound s t hs ht.le) hg (norm_nonneg _)
        CE.bound_nonneg
    _ = (CE.boundConst * Cnl * ‖q‖) * t ^ (-p - 1 - delta) := by ring

theorem weightedCenterNonlinearTail_bound
    {s0 p delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q : CenterWeightedPath s0 p) {s : ℝ} (hs : s0 ≤ s) :
    ‖weightedCenterNonlinearTail CE G p q s‖ ≤
      (CE.boundConst * Cnl * ‖q‖) / (p + delta) *
        s ^ (-p - delta) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hi := weightedCenterNonlinearSource_integrable
    CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q hs
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-p - 1 - delta)) (Ioi s) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hsp
  have hmajor := hpow.const_mul (CE.boundConst * Cnl * ‖q‖)
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi s),
      ‖weightedCenterNonlinearSource CE G p q s t‖ ≤
        (CE.boundConst * Cnl * ‖q‖) * t ^ (-p - 1 - delta) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hg := nonlinearPrimitive_bound G hs0 hCnl hGzero hGlip q (hs.trans ht.le)
    calc
      ‖weightedCenterNonlinearSource CE G p q s t‖
          ≤ ‖CE.U s t‖ * ‖G t (unweightPathGlobal p s0 q t)‖ :=
            (CE.U s t).le_opNorm _
      _ ≤ CE.boundConst * ((Cnl * ‖q‖) * t ^ (-p - 1 - delta)) := by
        exact mul_le_mul (CE.bound s t hs ht.le) hg (norm_nonneg _)
          CE.bound_nonneg
      _ = (CE.boundConst * Cnl * ‖q‖) * t ^ (-p - 1 - delta) := by ring
  have hI : (∫ t in Ioi s, t ^ (-p - 1 - delta)) =
      s ^ (-p - delta) / (p + delta) := by
    have h1 : -1 - (p + delta) = -p - 1 - delta := by ring
    have h2 : -(p + delta) = -p - delta := by ring
    simpa only [h1,h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀ := s) (δ := p + delta) hsp (by linarith))
  unfold weightedCenterNonlinearTail
  rw [norm_neg]
  calc
    ‖∫ t in Ioi s, weightedCenterNonlinearSource CE G p q s t‖
        ≤ ∫ t in Ioi s,
            (CE.boundConst * Cnl * ‖q‖) * t ^ (-p - 1 - delta) :=
          norm_integral_le_of_norm_le hmajor hpoint
    _ = (CE.boundConst * Cnl * ‖q‖) *
          (s ^ (-p - delta) / (p + delta)) := by
          rw [integral_const_mul,hI]
    _ = (CE.boundConst * Cnl * ‖q‖) / (p + delta) *
          s ^ (-p - delta) := by ring

theorem weightedCenterNonlinearTail_continuousOn
    {s0 p delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q : CenterWeightedPath s0 p) :
    ContinuousOn (weightedCenterNonlinearTail CE G p q) (Ici s0) := by
  let F : ℝ → ConstrainedCenterSpace :=
    fun t => G t (unweightPathGlobal p s0 q t)
  have hF : Continuous F := nonlinearPrimitive_continuous G hs0 hGcont q
  have hInt : ∀ s, s0 ≤ s →
      IntegrableOn (fun t => CE.U s t (F t)) (Ioi s) := by
    intro s hs
    exact weightedCenterNonlinearSource_integrable
      CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q hs
  exact CE.duhamel_continuous F hF hInt

def weightedCenterNonlinearValue
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (p : ℝ) (q : CenterWeightedPath s0 p)
    (s : LateTime s0) : ConstrainedCenterSpace :=
  ((s : ℝ) ^ p) • weightedCenterNonlinearTail CE G p q s

theorem weightedCenterNonlinearValue_continuous
    {s0 p delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q : CenterWeightedPath s0 p) :
    Continuous (weightedCenterNonlinearValue CE G p q) := by
  have htail :
      Continuous (fun s : LateTime s0 =>
        weightedCenterNonlinearTail CE G p q s) :=
    (weightedCenterNonlinearTail_continuousOn
      CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q).domRestrict
  apply continuous_iff_continuousAt.2
  intro s
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have hpow :
      ContinuousAt (fun t : LateTime s0 => ((t : ℝ) ^ p)) s := by
    exact (Real.continuousAt_rpow_const (s : ℝ) p
      (Or.inl hspos.ne')).comp continuousAt_subtype_val
  exact hpow.smul htail.continuousAt

theorem weightedCenterNonlinearValue_bound
    {s0 p delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q : CenterWeightedPath s0 p) (s : LateTime s0) :
    ‖weightedCenterNonlinearValue CE G p q s‖ ≤
      centerNonlinearLipschitzConstant CE p delta Cnl * ‖q‖ := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have ht := weightedCenterNonlinearTail_bound
    CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q s.2
  unfold weightedCenterNonlinearValue centerNonlinearLipschitzConstant
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hspos _)]
  have hpow : (s : ℝ) ^ p * (s : ℝ) ^ (-p - delta) =
      (s : ℝ) ^ (-delta) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring
  have hmono : (s : ℝ) ^ (-delta) ≤ s0 ^ (-delta) :=
    Real.rpow_le_rpow_of_nonpos hs0 s.2 (by linarith)
  have hden : 0 < p + delta := by linarith
  have hnum : 0 ≤ CE.boundConst * Cnl * ‖q‖ :=
    mul_nonneg (mul_nonneg CE.bound_nonneg hCnl) (norm_nonneg _)
  have hc : 0 ≤ (CE.boundConst * Cnl * ‖q‖) / (p + delta) :=
    div_nonneg hnum hden.le
  calc
    (s : ℝ) ^ p * ‖weightedCenterNonlinearTail CE G p q s‖
        ≤ (s : ℝ) ^ p *
          ((CE.boundConst * Cnl * ‖q‖) / (p + delta) *
            (s : ℝ) ^ (-p - delta)) := by
          exact mul_le_mul_of_nonneg_left ht
            (Real.rpow_nonneg hspos.le _)
    _ = (CE.boundConst * Cnl * ‖q‖) / (p + delta) *
          (s : ℝ) ^ (-delta) := by rw [← hpow]; ring
    _ ≤ (CE.boundConst * Cnl * ‖q‖) / (p + delta) *
          s0 ^ (-delta) := mul_le_mul_of_nonneg_left hmono hc
    _ = (CE.boundConst * Cnl) / (p + delta) *
          s0 ^ (-delta) * ‖q‖ := by ring

def weightedCenterNonlinearMap
    {s0 p delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖) :
    CenterWeightedPath s0 p → CenterWeightedPath s0 p :=
  fun q =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (weightedCenterNonlinearValue CE G p q)
      (weightedCenterNonlinearValue_continuous
        CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q)
      (centerNonlinearLipschitzConstant CE p delta Cnl * ‖q‖)
      (weightedCenterNonlinearValue_bound
        CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q)

theorem weightedCenterNonlinearMap_difference_norm
    {s0 p delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q r : CenterWeightedPath s0 p) :
    ‖weightedCenterNonlinearMap CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q -
        weightedCenterNonlinearMap CE G hs0 hp hdelta hCnl hGcont hGzero hGlip r‖ ≤
      centerNonlinearLipschitzConstant CE p delta Cnl * ‖q - r‖ := by
  have hC : 0 ≤ centerNonlinearLipschitzConstant CE p delta Cnl * ‖q-r‖ :=
    mul_nonneg
      (centerNonlinearLipschitzConstant_nonneg CE hs0 hp hdelta hCnl)
      (norm_nonneg _)
  rw [BoundedContinuousFunction.norm_le hC]
  intro s
  change ‖weightedCenterNonlinearValue CE G p q s -
      weightedCenterNonlinearValue CE G p r s‖ ≤ _
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have hdiff : ∀ t, s.1 ≤ t →
      ‖G t (unweightPathGlobal p s0 q t) -
        G t (unweightPathGlobal p s0 r t)‖ ≤
      (Cnl * ‖q-r‖) * t ^ (-p - 1 - delta) := by
    intro t ht
    have ht0 : s0 ≤ t := s.2.trans ht
    have hqr := unweightPathGlobal_norm_bound p s0 hs0 (q-r) ht0
    have heq : unweightPathGlobal p s0 q t -
        unweightPathGlobal p s0 r t =
        unweightPathGlobal p s0 (q-r) t := by
      unfold unweightPathGlobal
      simp only [BoundedContinuousFunction.sub_apply, smul_sub]
    have hg := hGlip t ht0 (unweightPathGlobal p s0 q t)
      (unweightPathGlobal p s0 r t)
    rw [heq] at hg
    have htpos : 0 < t := hs0.trans_le ht0
    have hmul :=
      mul_le_mul_of_nonneg_left hqr
        (mul_nonneg hCnl (Real.rpow_nonneg htpos.le _))
    have hpw : t ^ (-1-delta) * t ^ (-p) =
        t ^ (-p-1-delta) := by
      rw [← Real.rpow_add htpos]
      congr 1
      ring
    calc
      ‖G t (unweightPathGlobal p s0 q t) -
          G t (unweightPathGlobal p s0 r t)‖
          ≤ Cnl * t ^ (-1-delta) *
              ‖unweightPathGlobal p s0 (q-r) t‖ := hg
      _ ≤ Cnl * t ^ (-1-delta) * (‖q-r‖ * t ^ (-p)) := hmul
      _ = (Cnl * ‖q-r‖) * t ^ (-p-1-delta) := by
        rw [← hpw]
        ring
  have hmajor : IntegrableOn
      (fun t : ℝ => (CE.boundConst * Cnl * ‖q-r‖) *
        t ^ (-p-1-delta)) (Ioi (s : ℝ)) := by
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) hspos).const_mul _
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi (s : ℝ)),
      ‖CE.U s t
        (G t (unweightPathGlobal p s0 q t) -
         G t (unweightPathGlobal p s0 r t))‖ ≤
      (CE.boundConst * Cnl * ‖q-r‖) * t ^ (-p-1-delta) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      ‖CE.U s t (G t (unweightPathGlobal p s0 q t) -
          G t (unweightPathGlobal p s0 r t))‖
          ≤ ‖CE.U s t‖ *
              ‖G t (unweightPathGlobal p s0 q t) -
                G t (unweightPathGlobal p s0 r t)‖ :=
            (CE.U s t).le_opNorm _
      _ ≤ CE.boundConst *
          ((Cnl * ‖q-r‖) * t ^ (-p-1-delta)) := by
        exact mul_le_mul (CE.bound s t s.2 ht.le) (hdiff t ht.le)
          (norm_nonneg _) CE.bound_nonneg
      _ = _ := by ring
  have hI : (∫ t in Ioi (s : ℝ), t ^ (-p-1-delta)) =
      (s : ℝ) ^ (-p-delta) / (p+delta) := by
    have h1 : -1-(p+delta) = -p-1-delta := by ring
    have h2 : -(p+delta) = -p-delta := by ring
    simpa only [h1,h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀:=(s:ℝ)) (δ:=p+delta) hspos (by linarith))
  have hiq := weightedCenterNonlinearSource_integrable
    CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q s.2
  have hir := weightedCenterNonlinearSource_integrable
    CE G hs0 hp hdelta hCnl hGcont hGzero hGlip r s.2
  have hInt :
      (∫ t in Ioi (s : ℝ),
          weightedCenterNonlinearSource CE G p q s t) -
        (∫ t in Ioi (s : ℝ),
          weightedCenterNonlinearSource CE G p r s t) =
      ∫ t in Ioi (s : ℝ),
        CE.U s t
          (G t (unweightPathGlobal p s0 q t) -
            G t (unweightPathGlobal p s0 r t)) := by
    calc
      (∫ t in Ioi (s : ℝ),
          weightedCenterNonlinearSource CE G p q s t) -
        (∫ t in Ioi (s : ℝ),
          weightedCenterNonlinearSource CE G p r s t)
          = ∫ t in Ioi (s : ℝ),
              (weightedCenterNonlinearSource CE G p q s t -
                weightedCenterNonlinearSource CE G p r s t) := by
              symm
              exact integral_sub hiq hir
      _ = ∫ t in Ioi (s : ℝ),
          CE.U s t
            (G t (unweightPathGlobal p s0 q t) -
              G t (unweightPathGlobal p s0 r t)) := by
              apply integral_congr_ae
              filter_upwards with t
              unfold weightedCenterNonlinearSource
              rw [map_sub]
  have htail :
      ‖weightedCenterNonlinearTail CE G p q s -
        weightedCenterNonlinearTail CE G p r s‖ ≤
      (CE.boundConst*Cnl*‖q-r‖)/(p+delta) *
        (s:ℝ)^(-p-delta) := by
    unfold weightedCenterNonlinearTail
    rw [← hInt]
    rw [norm_neg]
    calc
      ‖∫ t in Ioi (s : ℝ),
          CE.U s t
            (G t (unweightPathGlobal p s0 q t) -
              G t (unweightPathGlobal p s0 r t))‖
          ≤ ∫ t in Ioi (s:ℝ),
              (CE.boundConst*Cnl*‖q-r‖) * t^(-p-1-delta) :=
            norm_integral_le_of_norm_le hmajor hpoint
      _ = (CE.boundConst*Cnl*‖q-r‖) *
          ((s:ℝ)^(-p-delta)/(p+delta)) := by
            rw [integral_const_mul,hI]
      _ = _ := by ring
  have hval :
      weightedCenterNonlinearValue CE G p q s -
      weightedCenterNonlinearValue CE G p r s =
      ((s:ℝ)^p) •
        (weightedCenterNonlinearTail CE G p q s -
         weightedCenterNonlinearTail CE G p r s) := by
    unfold weightedCenterNonlinearValue
    exact (smul_sub _ _ _).symm
  rw [hval,norm_smul,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hspos _)]
  have hpw : (s:ℝ)^p * (s:ℝ)^(-p-delta) =
      (s:ℝ)^(-delta) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring
  have hmono : (s:ℝ)^(-delta) ≤ s0^(-delta) :=
    Real.rpow_le_rpow_of_nonpos hs0 s.2 (by linarith)
  have hden2 : 0 < p + delta := by linarith
  have hnum2 : 0 ≤ CE.boundConst*Cnl*‖q-r‖ :=
    mul_nonneg (mul_nonneg CE.bound_nonneg hCnl) (norm_nonneg _)
  have hc : 0 ≤ (CE.boundConst*Cnl*‖q-r‖)/(p+delta) :=
    div_nonneg hnum2 hden2.le
  calc
    (s:ℝ)^p *
      ‖weightedCenterNonlinearTail CE G p q s -
        weightedCenterNonlinearTail CE G p r s‖
      ≤ (s:ℝ)^p *
        ((CE.boundConst*Cnl*‖q-r‖)/(p+delta) *
          (s:ℝ)^(-p-delta)) :=
        mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hspos.le _)
    _ = (CE.boundConst*Cnl*‖q-r‖)/(p+delta) *
        (s:ℝ)^(-delta) := by rw [← hpw]; ring
    _ ≤ (CE.boundConst*Cnl*‖q-r‖)/(p+delta) *
        s0^(-delta) := mul_le_mul_of_nonneg_left hmono hc
    _ = centerNonlinearLipschitzConstant CE p delta Cnl * ‖q-r‖ := by
      unfold centerNonlinearLipschitzConstant
      ring

theorem weightedCenterNonlinearMap_lipschitz
    {s0 p delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖) :
    LipschitzWith
      (Real.toNNReal (centerNonlinearLipschitzConstant CE p delta Cnl))
      (weightedCenterNonlinearMap CE G hs0 hp hdelta hCnl hGcont hGzero hGlip) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  have hnon : 0 ≤ centerNonlinearLipschitzConstant CE p delta Cnl :=
    centerNonlinearLipschitzConstant_nonneg CE hs0 hp hdelta hCnl
  simpa [dist_eq_norm, Real.coe_toNNReal _ hnon] using
    (weightedCenterNonlinearMap_difference_norm
      CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q r)

#print axioms weightedCenterNonlinearTail_bound
#print axioms weightedCenterNonlinearMap_difference_norm
#print axioms weightedCenterNonlinearMap_lipschitz

end HBL.MainBackward
