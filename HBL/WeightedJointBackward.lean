import HBL.JointBackwardContraction
import HBL.WeightedThresholdMap
import HBL.WeightedCenterFeedbackMap
import Mathlib.Tactic

/-!
# Actual weighted joint backward fixed point

This instantiates the generic Banach lemma on the genuine HBL weighted
centre and threshold path spaces.  Fixed high-order/profile/stable pieces are
allowed as affine translations; they do not change the contraction constant.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.MainBackward

def affineWeightedThresholdMap
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (a0 : ThresholdWeightedPath s0 p)
    (q : CenterWeightedPath s0 p) : ThresholdWeightedPath s0 p :=
  a0 + weightedThresholdMap B s0 p hs0 hp q

def affineWeightedCenterMap
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (q0 : CenterWeightedPath s0 p)
    (a : ThresholdWeightedPath s0 p) : CenterWeightedPath s0 p :=
  q0 + weightedCenterFeedbackMap CE E hs0 hp hnu hL hEcont hE a

theorem affineWeightedThresholdMap_lipschitz
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (a0 : ThresholdWeightedPath s0 p) :
    LipschitzWith (Real.toNNReal (‖B‖ / (p - 1)))
      (affineWeightedThresholdMap B s0 p hs0 hp a0) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  have h := (weightedThresholdMap_lipschitz B s0 p hs0 hp).dist_le_mul q r
  simpa [affineWeightedThresholdMap, dist_eq_norm] using h

theorem affineWeightedCenterMap_lipschitz
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (q0 : CenterWeightedPath s0 p) :
    LipschitzWith
      (Real.toNNReal (centerFeedbackLipschitzConstant CE p nu L))
      (affineWeightedCenterMap CE E hs0 hp hnu hL hEcont hE q0) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have h := (weightedCenterFeedbackMap_lipschitz
    CE E hs0 hp hnu hL hEcont hE).dist_le_mul a b
  simpa [affineWeightedCenterMap, dist_eq_norm] using h

private theorem contraction_constants_product
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu) (hL : 0 ≤ L)
    (hsmall :
      jointBackwardProduct p nu CE.boundConst L ‖B‖ s0 < 1) :
    Real.toNNReal (centerFeedbackLipschitzConstant CE p nu L) *
        Real.toNNReal (‖B‖ / (p - 1)) < 1 := by
  have hA : 0 ≤ ‖B‖ / (p - 1) := by positivity
  have hQ : 0 ≤ centerFeedbackLipschitzConstant CE p nu L :=
    centerFeedbackLipschitzConstant_nonneg CE hs0 hp hnu hL
  have heq :
      centerFeedbackLipschitzConstant CE p nu L *
          (‖B‖ / (p - 1)) =
        jointBackwardProduct p nu CE.boundConst L ‖B‖ s0 := by
    unfold centerFeedbackLipschitzConstant jointBackwardProduct
    ring
  rw [← heq] at hsmall
  exact_mod_cast hsmall

/-- Unique coupled weighted backward orbit for the actual HBL path spaces,
relative only to the standard constrained propagator boundary. -/
theorem weighted_joint_backward_fixed_point
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p)
    (hsmall :
      jointBackwardProduct p nu CE.boundConst L ‖B‖ s0 < 1) :
    ∃! z : CenterWeightedPath s0 p × ThresholdWeightedPath s0 p,
      z.2 = affineWeightedThresholdMap B s0 p hs0 hp a0 z.1 ∧
      z.1 = affineWeightedCenterMap
        CE E hs0 hp hnu hL hEcont hE q0 z.2 := by
  exact two_stage_backward_fixed_point
    (Real.toNNReal (‖B‖ / (p - 1)))
    (Real.toNNReal (centerFeedbackLipschitzConstant CE p nu L))
    (affineWeightedThresholdMap B s0 p hs0 hp a0)
    (affineWeightedCenterMap CE E hs0 hp hnu hL hEcont hE q0)
    (affineWeightedThresholdMap_lipschitz B s0 p hs0 hp a0)
    (affineWeightedCenterMap_lipschitz CE E hs0 hp hnu hL hEcont hE q0)
    (contraction_constants_product B CE hs0 hp hnu hL hsmall)

#print axioms affineWeightedThresholdMap_lipschitz
#print axioms affineWeightedCenterMap_lipschitz
#print axioms weighted_joint_backward_fixed_point

end HBL.MainBackward
