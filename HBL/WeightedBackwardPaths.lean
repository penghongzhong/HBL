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
      (Or.inl hspos.ne')).comp s continuousAt_subtype_val
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

#print axioms unweightPath_continuous
#print axioms unweightPath_norm_bound
#print axioms unweightPath_difference_bound
#print axioms unweightThresholdPath_difference_bound

end HBL.MainBackward
