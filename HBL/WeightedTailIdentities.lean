import HBL.WeightedThresholdMap
import HBL.WeightedCenterFeedbackMap
import HBL.WeightedCenterNonlinearMap
import HBL.WeightedAffineForcing
import Mathlib.Tactic

/-!
# Unweighting identities for the actual HBL backward paths

These identities convert the bounded weighted fixed-point variables back to
the genuine terminal tails. They are purely algebraic and use only positivity
of the late-time variable.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.MainBackward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem rpow_weight_unweight_cancel
    {s p : ℝ} (hs : 0 < s) (x : E) :
    s ^ (-p) • (s ^ p • x) = x := by
  rw [smul_smul]
  have hpow : s ^ (-p) * s ^ p = 1 := by
    rw [← Real.rpow_add hs]
    norm_num
  rw [hpow, one_smul]

/-- Unweighting the threshold map recovers its actual terminal tail. -/
theorem unweight_weightedThresholdMap
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q : CenterWeightedPath s0 p) (s : LateTime s0) :
    unweightThresholdPath s0 p
      (weightedThresholdMap B s0 p hs0 hp q) s =
      weightedThresholdTail B s0 p q s := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  change ((s : ℝ) ^ (-(p - 1))) •
      (((s : ℝ) ^ (p - 1)) •
        weightedThresholdTail B s0 p q s) =
      weightedThresholdTail B s0 p q s
  exact rpow_weight_unweight_cancel (E := ℝ × ℝ) hspos _

/-- Unweighting the threshold affine forcing recovers the actual forcing tail. -/
theorem unweight_weightedThresholdForcingPath
    (F : ℝ → ℝ × ℝ) (s0 p CF : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hCF : 0 ≤ CF)
    (hFcont : Continuous F)
    (hF : ∀ t, s0 ≤ t → ‖F t‖ ≤ CF * t ^ (-p - 1))
    (s : LateTime s0) :
    unweightThresholdPath s0 p
      (weightedThresholdForcingPath F s0 p CF
        hs0 hp hCF hFcont hF) s =
      weightedThresholdForcingTail F s := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  change ((s : ℝ) ^ (-(p - 1))) •
      (((s : ℝ) ^ (p - 1)) • weightedThresholdForcingTail F s) =
      weightedThresholdForcingTail F s
  exact rpow_weight_unweight_cancel (E := ℝ × ℝ) hspos _

/-- Unweighting the retained feedback map recovers the actual centre tail. -/
theorem unweight_weightedCenterFeedbackMap
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (Eop : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous Eop)
    (hE : ∀ t, s0 ≤ t → ‖Eop t‖ ≤ L * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p) (s : LateTime s0) :
    unweightCenterPath s0 p
      (weightedCenterFeedbackMap CE Eop hs0 hp hnu hL hEcont hE a) s =
      weightedCenterFeedbackTail CE Eop p a s := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  change ((s : ℝ) ^ (-p)) •
      (((s : ℝ) ^ p) • weightedCenterFeedbackTail CE Eop p a s) =
      weightedCenterFeedbackTail CE Eop p a s
  exact rpow_weight_unweight_cancel (E := ConstrainedCenterSpace) hspos _

/-- Unweighting the nonlinear centre map recovers the actual nonlinear tail. -/
theorem unweight_weightedCenterNonlinearMap
    {s0 p delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous
      (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤
        Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q : CenterWeightedPath s0 p) (s : LateTime s0) :
    unweightCenterPath s0 p
      (weightedCenterNonlinearMap CE G hs0 hp hdelta hCnl
        hGcont hGzero hGlip q) s =
      weightedCenterNonlinearTail CE G p q s := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  change ((s : ℝ) ^ (-p)) •
      (((s : ℝ) ^ p) • weightedCenterNonlinearTail CE G p q s) =
      weightedCenterNonlinearTail CE G p q s
  exact rpow_weight_unweight_cancel (E := ConstrainedCenterSpace) hspos _

/-- Unweighting the high-order centre forcing path recovers its Duhamel tail. -/
theorem unweight_weightedCenterForcingPath
    {s0 : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (F : ℝ → ConstrainedCenterSpace)
    (p N CF : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hN : p + 1 < N)
    (hCF : 0 ≤ CF) (hFcont : Continuous F)
    (hF : ∀ t, s0 ≤ t → ‖F t‖ ≤ CF * t ^ (-N))
    (s : LateTime s0) :
    unweightCenterPath s0 p
      (weightedCenterForcingPath CE F p N CF
        hs0 hp hN hCF hFcont hF) s =
      weightedCenterForcingTail CE F s := by
  have hspos : 0 < (s : ℝ) := hs0.trans_le s.2
  change ((s : ℝ) ^ (-p)) •
      (((s : ℝ) ^ p) • weightedCenterForcingTail CE F s) =
      weightedCenterForcingTail CE F s
  exact rpow_weight_unweight_cancel (E := ConstrainedCenterSpace) hspos _

#print axioms unweight_weightedThresholdMap
#print axioms unweight_weightedThresholdForcingPath
#print axioms unweight_weightedCenterFeedbackMap
#print axioms unweight_weightedCenterNonlinearMap
#print axioms unweight_weightedCenterForcingPath

end HBL.MainBackward
