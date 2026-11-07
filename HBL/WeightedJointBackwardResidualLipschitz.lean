import HBL.WeightedJointBackward
import HBL.WeightedThresholdResidualFeedback
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# Joint backward fixed point with direct threshold-residual Lipschitz feedback

This is the final-chain replacement for the older linear coefficient
E(t) = -D_theta R(t).  The threshold-to-centre coupling is now the actual
residual difference H(t,theta), with a direct weighted Lipschitz estimate.

The direct threshold-residual feedback dependency is now strict-audited.
Consequently the Banach construction no longer requires Frechet
differentiability of the finite profile residual.  The decay threshold remains
nu>2, exactly as in the previous linear formulation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace HBL.MainBackward

def fullWeightedCenterResidualLipschitzSelfMap
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖)
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous
      (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤
        Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p)
    (q : CenterWeightedPath s0 p) : CenterWeightedPath s0 p :=
  q0 +
    weightedThresholdResidualFeedbackMap
      CE H hs0 hp hnu hL hHcont hHzero hHlip
      (affineWeightedThresholdMap B s0 p hs0 hp a0 q) +
    weightedCenterNonlinearMap
      CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q

theorem fullWeightedCenterResidualLipschitzSelfMap_difference_norm
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖)
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous
      (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤
        Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p)
    (q r : CenterWeightedPath s0 p) :
    ‖fullWeightedCenterResidualLipschitzSelfMap
        B CE H G hs0 hp hnu hL hHcont hHzero hHlip
          hdelta hCnl hGcont hGzero hGlip q0 a0 q -
      fullWeightedCenterResidualLipschitzSelfMap
        B CE H G hs0 hp hnu hL hHcont hHzero hHlip
          hdelta hCnl hGcont hGzero hGlip q0 a0 r‖ ≤
      weightedJointLipschitzConstant B CE p nu L delta Cnl *
        ‖q-r‖ := by
  let A := affineWeightedThresholdMap B s0 p hs0 hp a0
  let Cfb :=
    weightedThresholdResidualFeedbackMap
      CE H hs0 hp hnu hL hHcont hHzero hHlip
  let CnlMap :=
    weightedCenterNonlinearMap
      CE G hs0 hp hdelta hCnl hGcont hGzero hGlip
  have hA :
      ‖A q - A r‖ ≤ (‖B‖ / (p - 1)) * ‖q-r‖ := by
    have h :=
      (affineWeightedThresholdMap_lipschitz
        B s0 p hs0 hp a0).dist_le_mul q r
    have hnon : 0 ≤ ‖B‖ / (p - 1) := by positivity
    rw [Real.coe_toNNReal _ hnon] at h
    have hout : dist (A q) (A r) = ‖A q - A r‖ := by
      rw [dist_eq_norm_sub]
    have hin := centerWeightedPath_dist_eq_norm_sub s0 p q r
    rw [hout, hin] at h
    exact h
  have hfb :
      ‖Cfb (A q) - Cfb (A r)‖ ≤
        centerFeedbackLipschitzConstant CE p nu L *
          ‖A q-A r‖ :=
    weightedThresholdResidualFeedbackMap_difference_norm
      CE H hs0 hp hnu hL hHcont hHzero hHlip (A q) (A r)
  have hfb' :
      ‖Cfb (A q) - Cfb (A r)‖ ≤
        (centerFeedbackLipschitzConstant CE p nu L *
          (‖B‖/(p-1))) * ‖q-r‖ := by
    exact hfb.trans
      (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hA
          (centerFeedbackLipschitzConstant_nonneg
            CE hs0 hp hnu hL))
  have hnl :
      ‖CnlMap q - CnlMap r‖ ≤
        centerNonlinearLipschitzConstant CE p delta Cnl *
          ‖q-r‖ :=
    weightedCenterNonlinearMap_difference_norm
      CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q r
  have hid :
      fullWeightedCenterResidualLipschitzSelfMap
          B CE H G hs0 hp hnu hL hHcont hHzero hHlip
            hdelta hCnl hGcont hGzero hGlip q0 a0 q -
        fullWeightedCenterResidualLipschitzSelfMap
          B CE H G hs0 hp hnu hL hHcont hHzero hHlip
            hdelta hCnl hGcont hGzero hGlip q0 a0 r =
      (Cfb (A q) - Cfb (A r)) +
        (CnlMap q-CnlMap r) := by
    dsimp [fullWeightedCenterResidualLipschitzSelfMap,
      A, Cfb, CnlMap]
    abel
  rw [hid]
  calc
    ‖(Cfb (A q) - Cfb (A r)) + (CnlMap q-CnlMap r)‖
        ≤ ‖Cfb (A q) - Cfb (A r)‖ +
            ‖CnlMap q-CnlMap r‖ := by
      have hN :
          0 ≤ ‖Cfb (A q) - Cfb (A r)‖ +
            ‖CnlMap q - CnlMap r‖ := by positivity
      apply (BoundedContinuousFunction.norm_le
        (f := (Cfb (A q) - Cfb (A r)) +
          (CnlMap q - CnlMap r)) hN).2
      intro t
      change
        ‖(Cfb (A q) - Cfb (A r)) t +
          (CnlMap q - CnlMap r) t‖ ≤ _
      exact (norm_add_le
        ((Cfb (A q) - Cfb (A r)) t)
        ((CnlMap q - CnlMap r) t)).trans
          (add_le_add
            ((Cfb (A q) - Cfb (A r)).norm_coe_le_norm t)
            ((CnlMap q - CnlMap r).norm_coe_le_norm t))
    _ ≤
        (centerFeedbackLipschitzConstant CE p nu L *
          (‖B‖/(p-1))) * ‖q-r‖ +
        centerNonlinearLipschitzConstant CE p delta Cnl *
          ‖q-r‖ :=
      add_le_add hfb' hnl
    _ = weightedJointLipschitzConstant
          B CE p nu L delta Cnl * ‖q-r‖ := by
      unfold weightedJointLipschitzConstant
      ring

theorem fullWeightedCenterResidualLipschitzSelfMap_lipschitz
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖)
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous
      (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤
        Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p) :
    LipschitzWith
      (Real.toNNReal
        (weightedJointLipschitzConstant
          B CE p nu L delta Cnl))
      (fullWeightedCenterResidualLipschitzSelfMap
        B CE H G hs0 hp hnu hL hHcont hHzero hHlip
          hdelta hCnl hGcont hGzero hGlip q0 a0) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  have hnon :=
    weightedJointLipschitzConstant_nonneg
      B CE hs0 hp hnu hL hdelta hCnl
  rw [Real.coe_toNNReal _ hnon]
  have hout :=
    centerWeightedPath_dist_eq_norm_sub s0 p
      (fullWeightedCenterResidualLipschitzSelfMap
        B CE H G hs0 hp hnu hL hHcont hHzero hHlip
          hdelta hCnl hGcont hGzero hGlip q0 a0 q)
      (fullWeightedCenterResidualLipschitzSelfMap
        B CE H G hs0 hp hnu hL hHcont hHzero hHlip
          hdelta hCnl hGcont hGzero hGlip q0 a0 r)
  have hin := centerWeightedPath_dist_eq_norm_sub s0 p q r
  rw [hout, hin]
  exact
    fullWeightedCenterResidualLipschitzSelfMap_difference_norm
      B CE H G hs0 hp hnu hL hHcont hHzero hHlip
        hdelta hCnl hGcont hGzero hGlip q0 a0 q r

theorem nonlinear_weighted_joint_backward_fixed_point_residual_lipschitz
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L)
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-nu) * ‖theta - eta‖)
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous
      (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤
        Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p)
    (hsmall :
      weightedJointLipschitzConstant
        B CE p nu L delta Cnl < 1) :
    ∃! z : CenterWeightedPath s0 p × ThresholdWeightedPath s0 p,
      z.2 = affineWeightedThresholdMap
        B s0 p hs0 hp a0 z.1 ∧
      z.1 =
        fullWeightedCenterResidualLipschitzSelfMap
          B CE H G hs0 hp hnu hL hHcont hHzero hHlip
            hdelta hCnl hGcont hGzero hGlip q0 a0 z.1 := by
  let Phi :=
    fullWeightedCenterResidualLipschitzSelfMap
      B CE H G hs0 hp hnu hL hHcont hHzero hHlip
        hdelta hCnl hGcont hGzero hGlip q0 a0
  have hnon :=
    weightedJointLipschitzConstant_nonneg
      B CE hs0 hp hnu hL hdelta hCnl
  have hK :
      Real.toNNReal
          (weightedJointLipschitzConstant
            B CE p nu L delta Cnl) < (1 : NNReal) :=
    (Real.toNNReal_lt_iff_lt_coe hnon).2
      (by simpa using hsmall)
  have hPhi : ContractingWith
      (Real.toNNReal
        (weightedJointLipschitzConstant
          B CE p nu L delta Cnl)) Phi :=
    ⟨hK,
      fullWeightedCenterResidualLipschitzSelfMap_lipschitz
        B CE H G hs0 hp hnu hL hHcont hHzero hHlip
          hdelta hCnl hGcont hGzero hGlip q0 a0⟩
  let qstar : CenterWeightedPath s0 p :=
    hPhi.fixedPoint Phi
  let astar :=
    affineWeightedThresholdMap
      B s0 p hs0 hp a0 qstar
  have hqstar : Phi qstar = qstar :=
    hPhi.fixedPoint_isFixedPt
  refine ⟨(qstar, astar), ?_, ?_⟩
  · exact ⟨rfl, hqstar.symm⟩
  · intro z hz
    rcases hz with ⟨hza, hzq⟩
    have hfix : Phi z.1 = z.1 := by
      simpa [Phi] using hzq.symm
    have hzqstar : z.1 = qstar := by
      change z.1 = hPhi.fixedPoint Phi
      exact hPhi.fixedPoint_unique hfix
    apply Prod.ext
    · exact hzqstar
    · rw [hza, hzqstar]

end HBL.MainBackward
