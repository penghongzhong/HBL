import HBL.WeightedThresholdMap
import HBL.WeightedCenterFeedbackMap
import HBL.WeightedCenterNonlinearMap
import HBL.WeightedAffineForcing
import Mathlib.Tactic

/-!
# Removing the late-time weights

These identities connect the Banach fixed point on weighted path spaces to
the actual Volterra/Duhamel tails.  They contain no PDE input.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.MainBackward

private theorem rpow_neg_smul_rpow_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s p : ℝ} (hs : 0 < s) (x : E) :
    (s ^ (-p)) • ((s ^ p) • x) = x := by
  rw [smul_smul]
  have hp : s ^ (-p) * s ^ p = 1 := by
    rw [← Real.rpow_add hs]
    simp
  rw [hp, one_smul]

theorem unweight_weightedThresholdMap_eq_tail
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q : CenterWeightedPath s0 p) (s : LateTime s0) :
    unweightThresholdPath s0 p
        (weightedThresholdMap B s0 p hs0 hp q) s =
      weightedThresholdTail B s0 p q s := by
  have hs : 0 < (s : ℝ) := hs0.trans_le s.2
  change ((s : ℝ) ^ (-(p - 1))) •
      (((s : ℝ) ^ (p - 1)) • weightedThresholdTail B s0 p q s) =
    weightedThresholdTail B s0 p q s
  exact rpow_neg_smul_rpow_smul hs _

theorem unweight_weightedCenterFeedbackMap_eq_tail
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p) (s : LateTime s0) :
    unweightCenterPath s0 p
        (weightedCenterFeedbackMap CE E hs0 hp hnu hL hEcont hE a) s =
      weightedCenterFeedbackTail CE E p a s := by
  have hs : 0 < (s : ℝ) := hs0.trans_le s.2
  change ((s : ℝ) ^ (-p)) •
      (((s : ℝ) ^ p) • weightedCenterFeedbackTail CE E p a s) =
    weightedCenterFeedbackTail CE E p a s
  exact rpow_neg_smul_rpow_smul hs _

theorem unweight_weightedCenterNonlinearMap_eq_tail
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
    unweightCenterPath s0 p
        (weightedCenterNonlinearMap CE G
          hs0 hp hdelta hCnl hGcont hGzero hGlip q) s =
      weightedCenterNonlinearTail CE G p q s := by
  have hs : 0 < (s : ℝ) := hs0.trans_le s.2
  change ((s : ℝ) ^ (-p)) •
      (((s : ℝ) ^ p) • weightedCenterNonlinearTail CE G p q s) =
    weightedCenterNonlinearTail CE G p q s
  exact rpow_neg_smul_rpow_smul hs _

theorem unweight_weightedThresholdForcingPath_eq_tail
    (F : ℝ → ℝ × ℝ) (s0 p CF : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hCF : 0 ≤ CF)
    (hFcont : Continuous F)
    (hF : ∀ t, s0 ≤ t → ‖F t‖ ≤ CF * t ^ (-p-1))
    (s : LateTime s0) :
    unweightThresholdPath s0 p
        (weightedThresholdForcingPath F s0 p CF hs0 hp hCF hFcont hF) s =
      weightedThresholdForcingTail F s := by
  have hs : 0 < (s : ℝ) := hs0.trans_le s.2
  change ((s : ℝ) ^ (-(p - 1))) •
      (((s : ℝ) ^ (p - 1)) • weightedThresholdForcingTail F s) =
    weightedThresholdForcingTail F s
  exact rpow_neg_smul_rpow_smul hs _

theorem unweight_weightedCenterForcingPath_eq_tail
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (F : ℝ → ConstrainedCenterSpace)
    (p N CF : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hN : p+1 < N)
    (hCF : 0 ≤ CF) (hFcont : Continuous F)
    (hF : ∀ t, s0 ≤ t → ‖F t‖ ≤ CF*t^(-N))
    (s : LateTime s0) :
    unweightCenterPath s0 p
        (weightedCenterForcingPath CE F p N CF hs0 hp hN hCF hFcont hF) s =
      weightedCenterForcingTail CE F s := by
  have hs : 0 < (s : ℝ) := hs0.trans_le s.2
  change ((s : ℝ) ^ (-p)) •
      (((s : ℝ) ^ p) • weightedCenterForcingTail CE F s) =
    weightedCenterForcingTail CE F s
  exact rpow_neg_smul_rpow_smul hs _

#print axioms unweight_weightedThresholdMap_eq_tail
#print axioms unweight_weightedCenterFeedbackMap_eq_tail
#print axioms unweight_weightedCenterNonlinearMap_eq_tail
#print axioms unweight_weightedThresholdForcingPath_eq_tail
#print axioms unweight_weightedCenterForcingPath_eq_tail

end HBL.MainBackward
