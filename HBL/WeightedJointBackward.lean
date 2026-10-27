import HBL.JointBackwardContraction
import HBL.WeightedThresholdMap
import HBL.WeightedCenterFeedbackMap
import HBL.WeightedCenterNonlinearMap
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

/-- Exact Lipschitz constant of the full repaired centre self-map:
threshold feedback followed by threshold reconstruction, plus the direct
nonlinear centre term. -/
def weightedJointLipschitzConstant
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (p nu L delta Cnl : ℝ) : ℝ :=
  centerFeedbackLipschitzConstant CE p nu L * (‖B‖ / (p - 1)) +
    centerNonlinearLipschitzConstant CE p delta Cnl

theorem weightedJointLipschitzConstant_nonneg
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl) :
    0 ≤ weightedJointLipschitzConstant B CE p nu L delta Cnl := by
  unfold weightedJointLipschitzConstant
  have hfb := centerFeedbackLipschitzConstant_nonneg CE hs0 hp hnu hL
  have hth : 0 ≤ ‖B‖ / (p - 1) := by positivity
  have hnl := centerNonlinearLipschitzConstant_nonneg CE hs0 hp hdelta hCnl
  positivity

/-- The actual nonlinear weighted centre self-map. -/
def fullWeightedCenterSelfMap
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p)
    (q : CenterWeightedPath s0 p) : CenterWeightedPath s0 p :=
  q0 +
    weightedCenterFeedbackMap CE E hs0 hp hnu hL hEcont hE
      (affineWeightedThresholdMap B s0 p hs0 hp a0 q) +
    weightedCenterNonlinearMap CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q

theorem fullWeightedCenterSelfMap_difference_norm
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p)
    (q r : CenterWeightedPath s0 p) :
    ‖fullWeightedCenterSelfMap B CE E G hs0 hp hnu hL hEcont hE
          hdelta hCnl hGcont hGzero hGlip q0 a0 q -
        fullWeightedCenterSelfMap B CE E G hs0 hp hnu hL hEcont hE
          hdelta hCnl hGcont hGzero hGlip q0 a0 r‖ ≤
      weightedJointLipschitzConstant B CE p nu L delta Cnl * ‖q-r‖ := by
  let A := affineWeightedThresholdMap B s0 p hs0 hp a0
  let Cfb := weightedCenterFeedbackMap CE E hs0 hp hnu hL hEcont hE
  let CnlMap :=
    weightedCenterNonlinearMap CE G hs0 hp hdelta hCnl hGcont hGzero hGlip
  have hA :
      ‖A q - A r‖ ≤ (‖B‖ / (p-1)) * ‖q-r‖ := by
    have h := (affineWeightedThresholdMap_lipschitz B s0 p hs0 hp a0).dist_le_mul q r
    have hnon : 0 ≤ ‖B‖/(p-1) := by positivity
    simpa [A, dist_eq_norm, Real.coe_toNNReal _ hnon] using h
  have hfb :
      ‖Cfb (A q) - Cfb (A r)‖ ≤
        centerFeedbackLipschitzConstant CE p nu L * ‖A q-A r‖ :=
    weightedCenterFeedbackMap_difference_norm
      CE E hs0 hp hnu hL hEcont hE (A q) (A r)
  have hfb' :
      ‖Cfb (A q) - Cfb (A r)‖ ≤
        (centerFeedbackLipschitzConstant CE p nu L * (‖B‖/(p-1))) *
          ‖q-r‖ := by
    exact hfb.trans
      (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hA
          (centerFeedbackLipschitzConstant_nonneg CE hs0 hp hnu hL))
  have hnl :
      ‖CnlMap q - CnlMap r‖ ≤
        centerNonlinearLipschitzConstant CE p delta Cnl * ‖q-r‖ :=
    weightedCenterNonlinearMap_difference_norm
      CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q r
  have hid :
      fullWeightedCenterSelfMap B CE E G hs0 hp hnu hL hEcont hE
          hdelta hCnl hGcont hGzero hGlip q0 a0 q -
        fullWeightedCenterSelfMap B CE E G hs0 hp hnu hL hEcont hE
          hdelta hCnl hGcont hGzero hGlip q0 a0 r =
      (Cfb (A q) - Cfb (A r)) + (CnlMap q-CnlMap r) := by
    dsimp [fullWeightedCenterSelfMap, A, Cfb, CnlMap]
    abel
  rw [hid]
  calc
    ‖(Cfb (A q) - Cfb (A r)) + (CnlMap q-CnlMap r)‖
        ≤ ‖Cfb (A q) - Cfb (A r)‖ + ‖CnlMap q-CnlMap r‖ :=
          norm_add_le _ _
    _ ≤ (centerFeedbackLipschitzConstant CE p nu L * (‖B‖/(p-1))) *
          ‖q-r‖ +
        centerNonlinearLipschitzConstant CE p delta Cnl * ‖q-r‖ :=
          add_le_add hfb' hnl
    _ = weightedJointLipschitzConstant B CE p nu L delta Cnl * ‖q-r‖ := by
          unfold weightedJointLipschitzConstant
          ring

theorem fullWeightedCenterSelfMap_lipschitz
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p) :
    LipschitzWith
      (Real.toNNReal (weightedJointLipschitzConstant B CE p nu L delta Cnl))
      (fullWeightedCenterSelfMap B CE E G hs0 hp hnu hL hEcont hE
        hdelta hCnl hGcont hGzero hGlip q0 a0) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  have hnon := weightedJointLipschitzConstant_nonneg
    B CE hs0 hp hnu hL hdelta hCnl
  rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ hnon]
  exact fullWeightedCenterSelfMap_difference_norm B CE E G
    hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero hGlip q0 a0 q r

/-- Unique genuine nonlinear weighted centre path; the threshold path is then
recovered by the actual weighted threshold map. -/
theorem nonlinear_weighted_joint_backward_fixed_point
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p)
    (hsmall : weightedJointLipschitzConstant B CE p nu L delta Cnl < 1) :
    ∃! z : CenterWeightedPath s0 p × ThresholdWeightedPath s0 p,
      z.2 = affineWeightedThresholdMap B s0 p hs0 hp a0 z.1 ∧
      z.1 = fullWeightedCenterSelfMap B CE E G hs0 hp hnu hL hEcont hE
        hdelta hCnl hGcont hGzero hGlip q0 a0 z.1 := by
  let Phi := fullWeightedCenterSelfMap B CE E G hs0 hp hnu hL hEcont hE
    hdelta hCnl hGcont hGzero hGlip q0 a0
  have hnon := weightedJointLipschitzConstant_nonneg
    B CE hs0 hp hnu hL hdelta hCnl
  have hK :
      Real.toNNReal (weightedJointLipschitzConstant B CE p nu L delta Cnl) <
        (1 : NNReal) :=
    (Real.toNNReal_lt_iff_lt_coe hnon).2 (by simpa using hsmall)
  have hPhi : ContractingWith
      (Real.toNNReal (weightedJointLipschitzConstant B CE p nu L delta Cnl))
      Phi :=
    ⟨hK, fullWeightedCenterSelfMap_lipschitz B CE E G
      hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero hGlip q0 a0⟩
  let qstar : CenterWeightedPath s0 p := hPhi.fixedPoint Phi
  let astar := affineWeightedThresholdMap B s0 p hs0 hp a0 qstar
  have hqstar : Phi qstar = qstar := hPhi.fixedPoint_isFixedPt
  refine ⟨(qstar,astar), ?_, ?_⟩
  · exact ⟨rfl,hqstar.symm⟩
  · intro z hz
    rcases hz with ⟨hza,hzq⟩
    have hfix : Phi z.1 = z.1 := by
      simpa [Phi] using hzq.symm
    have hzqstar : z.1 = qstar := by
      change z.1 = hPhi.fixedPoint Phi
      exact hPhi.fixedPoint_unique hfix
    apply Prod.ext
    · exact hzqstar
    · rw [hza,hzqstar]
      rfl

#print axioms affineWeightedThresholdMap_lipschitz
#print axioms affineWeightedCenterMap_lipschitz
#print axioms weighted_joint_backward_fixed_point
#print axioms weightedJointLipschitzConstant
#print axioms fullWeightedCenterSelfMap_difference_norm
#print axioms nonlinear_weighted_joint_backward_fixed_point

end HBL.MainBackward
