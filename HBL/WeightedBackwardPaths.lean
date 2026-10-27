import HBL.ConstrainedCenterSpace
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# Weighted late-time path spaces

The repaired backward argument uses two concrete complete Banach spaces:
a centre path q(s)=O(s^{-p}) and a threshold path a(s)=O(s^{1-p}).
They are represented by bounded continuous weighted profiles on the actual
half-line [s0,infinity).
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace HBL.MainBackward

/-- The actual late-time half-line. -/
abbrev LateTime (s0 : ℝ) := Ici s0

/-- A bounded continuous weighted path. -/
abbrev WeightedPath (s0 : ℝ) (E : Type*)
    [TopologicalSpace E] [PseudoMetricSpace E] :=
  BoundedContinuousFunction (LateTime s0) E

/-- Continuous projection of the full real line onto the late-time half-line. -/
def lateTimeClamp (s0 : ℝ) (t : ℝ) : LateTime s0 :=
  ⟨max s0 t, by simpa only [mem_Ici] using le_max_left s0 t⟩

theorem lateTimeClamp_continuous (s0 : ℝ) :
    Continuous (lateTimeClamp s0) := by
  exact Continuous.subtype_mk (continuous_const.max continuous_id)
    (fun t => by simpa only [mem_Ici] using le_max_left s0 t)

/-- Global clamped representative of a weighted path.  On t>=s0 it agrees
with the genuine unweighted late-time path. -/
def unweightPathGlobal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p s0 : ℝ) (q : WeightedPath s0 E) (t : ℝ) : E :=
  ((max s0 t) ^ (-p)) • q (lateTimeClamp s0 t)

theorem unweightPathGlobal_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p s0 : ℝ) (hs0 : 0 < s0) (q : WeightedPath s0 E) :
    Continuous (unweightPathGlobal p s0 q) := by
  apply continuous_iff_continuousAt.2
  intro t
  have hmpos : 0 < max s0 t := hs0.trans_le (le_max_left _ _)
  have hp : ContinuousAt (fun x : ℝ => (max s0 x) ^ (-p)) t := by
    exact (Real.continuousAt_rpow_const (max s0 t) (-p)
      (Or.inl hmpos.ne')).comp
        (continuous_const.max continuous_id).continuousAt
  have hq :
      ContinuousAt (fun x : ℝ => q (lateTimeClamp s0 x)) t :=
    q.continuous.continuousAt.comp (lateTimeClamp_continuous s0).continuousAt
  exact hp.smul hq

theorem unweightPathGlobal_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p s0 : ℝ) (q : WeightedPath s0 E)
    {t : ℝ} (ht : s0 ≤ t) :
    unweightPathGlobal p s0 q t =
      t ^ (-p) • q ⟨t, ht⟩ := by
  have hclamp : lateTimeClamp s0 t = (⟨t, ht⟩ : LateTime s0) := by
    apply Subtype.ext
    simp [lateTimeClamp, max_eq_right ht]
  rw [unweightPathGlobal, max_eq_right ht, hclamp]

theorem unweightPathGlobal_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p s0 : ℝ) (hs0 : 0 < s0)
    (q : WeightedPath s0 E)
    {t : ℝ} (ht : s0 ≤ t) :
    ‖unweightPathGlobal p s0 q t‖ ≤ ‖q‖ * t ^ (-p) := by
  rw [unweightPathGlobal_eq p s0 q ht, norm_smul, Real.norm_eq_abs]
  have htpos : 0 < t := hs0.trans_le ht
  rw [abs_of_pos (Real.rpow_pos_of_pos htpos _)]
  have hq := q.norm_coe_le_norm ⟨t, ht⟩
  nlinarith [Real.rpow_pos_of_pos htpos (-p)]

/-- Recover an s^{-p} path from its bounded weighted representative. -/
def unweightPath
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p s0 : ℝ) (q : WeightedPath s0 E) (s : LateTime s0) : E :=
  ((s : ℝ) ^ (-p)) • q s

theorem unweightPath_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p s0 : ℝ) (hs0 : 0 < s0) (q : WeightedPath s0 E) :
    Continuous (unweightPath p s0 q) := by
  apply continuous_iff_continuousAt.2
  intro s
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have hp :
      ContinuousAt (fun t : LateTime s0 => ((t : ℝ) ^ (-p))) s := by
    exact (Real.continuousAt_rpow_const (s : ℝ) (-p)
      (Or.inl hspos.ne')).comp continuousAt_subtype_val
  exact hp.smul q.continuous.continuousAt

theorem unweightPath_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p s0 : ℝ) (hs0 : 0 < s0)
    (q : WeightedPath s0 E) (s : LateTime s0) :
    ‖unweightPath p s0 q s‖ ≤ ‖q‖ * (s : ℝ) ^ (-p) := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  rw [unweightPath, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hspos _)]
  have hq := q.norm_coe_le_norm s
  nlinarith [Real.rpow_pos_of_pos hspos (-p)]

theorem unweightPath_difference_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p s0 : ℝ) (hs0 : 0 < s0)
    (q r : WeightedPath s0 E) (s : LateTime s0) :
    ‖unweightPath p s0 q s - unweightPath p s0 r s‖ ≤
      ‖q - r‖ * (s : ℝ) ^ (-p) := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  have hid :
      unweightPath p s0 q s - unweightPath p s0 r s =
        ((s : ℝ) ^ (-p)) • ((q - r) s) := by
    simp only [unweightPath, BoundedContinuousFunction.sub_apply, smul_sub]
  rw [hid, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hspos _)]
  have hqr := (q - r).norm_coe_le_norm s
  nlinarith [Real.rpow_pos_of_pos hspos (-p)]

/-- Centre path: q(s)=s^{-p} qhat(s). -/
abbrev CenterWeightedPath (s0 p : ℝ) :=
  WeightedPath s0 ConstrainedCenterSpace

/-- Threshold path: a(s)=s^{1-p} ahat(s). -/
abbrev ThresholdWeightedPath (s0 p : ℝ) :=
  WeightedPath s0 (ℝ × ℝ)

def unweightCenterPath (s0 p : ℝ)
    (q : CenterWeightedPath s0 p) (s : LateTime s0) :
    ConstrainedCenterSpace :=
  unweightPath p s0 q s

def unweightThresholdPath (s0 p : ℝ)
    (a : ThresholdWeightedPath s0 p) (s : LateTime s0) :
    ℝ × ℝ :=
  unweightPath (p - 1) s0 a s

def unweightThresholdPathGlobal (s0 p : ℝ)
    (a : ThresholdWeightedPath s0 p) (t : ℝ) : ℝ × ℝ :=
  unweightPathGlobal (p - 1) s0 a t

theorem unweightThresholdPathGlobal_continuous
    (s0 p : ℝ) (hs0 : 0 < s0)
    (a : ThresholdWeightedPath s0 p) :
    Continuous (unweightThresholdPathGlobal s0 p a) := by
  exact unweightPathGlobal_continuous (p - 1) s0 hs0 a

theorem unweightThresholdPathGlobal_norm_bound
    (s0 p : ℝ) (hs0 : 0 < s0)
    (a : ThresholdWeightedPath s0 p)
    {t : ℝ} (ht : s0 ≤ t) :
    ‖unweightThresholdPathGlobal s0 p a t‖ ≤
      ‖a‖ * t ^ (1 - p) := by
  have h := unweightPathGlobal_norm_bound (p - 1) s0 hs0 a ht
  have he : -(p - 1) = 1 - p := by ring
  simpa only [unweightThresholdPathGlobal, he] using h

theorem unweightThresholdPathGlobal_difference_bound
    (s0 p : ℝ) (hs0 : 0 < s0)
    (a b : ThresholdWeightedPath s0 p)
    {t : ℝ} (ht : s0 ≤ t) :
    ‖unweightThresholdPathGlobal s0 p a t -
        unweightThresholdPathGlobal s0 p b t‖ ≤
      ‖a - b‖ * t ^ (1 - p) := by
  have h := unweightPathGlobal_norm_bound (p - 1) s0 hs0 (a - b) ht
  have heq :
      unweightThresholdPathGlobal s0 p a t -
          unweightThresholdPathGlobal s0 p b t =
        unweightPathGlobal (p - 1) s0 (a - b) t := by
    unfold unweightThresholdPathGlobal unweightPathGlobal
    simp only [BoundedContinuousFunction.sub_apply, smul_sub]
  rw [heq]
  have he : -(p - 1) = 1 - p := by ring
  simpa only [he] using h

theorem unweightThresholdPath_norm_bound
    (s0 p : ℝ) (hs0 : 0 < s0)
    (a : ThresholdWeightedPath s0 p) (s : LateTime s0) :
    ‖unweightThresholdPath s0 p a s‖ ≤
      ‖a‖ * (s : ℝ) ^ (1 - p) := by
  have h := unweightPath_norm_bound (p - 1) s0 hs0 a s
  have he : -(p - 1) = 1 - p := by ring
  simpa only [unweightThresholdPath, he] using h

theorem unweightThresholdPath_difference_bound
    (s0 p : ℝ) (hs0 : 0 < s0)
    (a b : ThresholdWeightedPath s0 p) (s : LateTime s0) :
    ‖unweightThresholdPath s0 p a s -
        unweightThresholdPath s0 p b s‖ ≤
      ‖a - b‖ * (s : ℝ) ^ (1 - p) := by
  have h := unweightPath_difference_bound (p - 1) s0 hs0 a b s
  have he : -(p - 1) = 1 - p := by ring
  simpa only [unweightThresholdPath, he] using h

#print axioms lateTimeClamp_continuous
#print axioms unweightPathGlobal_continuous
#print axioms unweightPathGlobal_norm_bound
#print axioms unweightPath_continuous
#print axioms unweightPath_norm_bound
#print axioms unweightPath_difference_bound
#print axioms unweightThresholdPathGlobal_difference_bound
#print axioms unweightThresholdPath_difference_bound

end HBL.MainBackward
