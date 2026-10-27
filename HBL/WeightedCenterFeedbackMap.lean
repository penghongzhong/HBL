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

end HBL.MainBackward
