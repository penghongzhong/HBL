import HBL.CoupledThresholdMap
import HBL.WeightedCenterFeedbackMap
import HBL.WeightedCenterNonlinearMap
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# Fully coupled nonlinear weighted backward map

This is the actual repaired late-time fixed point:
* the threshold equation retains its self-coupling ell E a and is solved
  first by a Volterra contraction;
* the centre equation sees the resulting threshold path;
* the direct nonlinear centre term is retained.

The exact Lipschitz constant is
  K_nl + K_fb * K_th / (1-K_self).
-/

noncomputable section
set_option autoImplicit false

namespace HBL.MainBackward

def fullyCoupledCenterLipschitzConstant
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (p nu L delta Cnl Lc : ℝ) : ℝ :=
  centerFeedbackLipschitzConstant CE p nu L *
      ((‖B‖ / (p-1)) /
        (1-thresholdSelfLipschitzConstant s0 p nu Lc)) +
    centerNonlinearLipschitzConstant CE p delta Cnl

theorem fullyCoupledCenterLipschitzConstant_nonneg
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl Lc : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hLc : 0 ≤ Lc)
    (hself : thresholdSelfLipschitzConstant s0 p nu Lc < 1) :
    0 ≤ fullyCoupledCenterLipschitzConstant
      B CE p nu L delta Cnl Lc := by
  unfold fullyCoupledCenterLipschitzConstant
  have hfb := centerFeedbackLipschitzConstant_nonneg CE hs0 hp hnu hL
  have hnl := centerNonlinearLipschitzConstant_nonneg CE hs0 hp hdelta hCnl
  have hth : 0 ≤ ‖B‖/(p-1) := by positivity
  have hden : 0 < 1-thresholdSelfLipschitzConstant s0 p nu Lc :=
    sub_pos.mpr hself
  have hquot : 0 ≤ (‖B‖/(p-1)) /
      (1-thresholdSelfLipschitzConstant s0 p nu Lc) :=
    div_nonneg hth hden.le
  positivity

def fullyCoupledCenterSelfMap
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl Lc : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L*t^(-nu))
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z-G t w‖ ≤ Cnl*t^(-1-delta)*‖z-w‖)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc*t^(-nu))
    (hself : thresholdSelfLipschitzConstant s0 p nu Lc < 1)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p)
    (q : CenterWeightedPath s0 p) : CenterWeightedPath s0 p :=
  q0 +
    weightedCenterFeedbackMap CE E hs0 hp hnu hL hEcont hE
      (coupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 hself q) +
    weightedCenterNonlinearMap CE G
      hs0 hp hdelta hCnl hGcont hGzero hGlip q

theorem fullyCoupledCenterSelfMap_difference_norm
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl Lc : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L*t^(-nu))
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z-G t w‖ ≤ Cnl*t^(-1-delta)*‖z-w‖)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc*t^(-nu))
    (hself : thresholdSelfLipschitzConstant s0 p nu Lc < 1)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p)
    (q r : CenterWeightedPath s0 p) :
    ‖fullyCoupledCenterSelfMap B C CE E G
          hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero hGlip
          hLc hCcont hC hself q0 a0 q -
        fullyCoupledCenterSelfMap B C CE E G
          hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero hGlip
          hLc hCcont hC hself q0 a0 r‖ ≤
      fullyCoupledCenterLipschitzConstant
        B CE p nu L delta Cnl Lc * ‖q-r‖ := by
  let Aq := coupledThresholdMap
    B C hs0 hp hnu hLc hCcont hC a0 hself
  let Cfb := weightedCenterFeedbackMap CE E hs0 hp hnu hL hEcont hE
  let CnlMap :=
    weightedCenterNonlinearMap CE G hs0 hp hdelta hCnl hGcont hGzero hGlip
  have hA :
      ‖Aq q-Aq r‖ ≤
        ((‖B‖/(p-1)) /
          (1-thresholdSelfLipschitzConstant s0 p nu Lc))*‖q-r‖ := by
    dsimp [Aq]
    exact coupledThresholdMap_difference_norm
      B C hs0 hp hnu hLc hCcont hC a0 hself q r
  have hfb :
      ‖Cfb (Aq q)-Cfb (Aq r)‖ ≤
        centerFeedbackLipschitzConstant CE p nu L * ‖Aq q-Aq r‖ :=
    weightedCenterFeedbackMap_difference_norm
      CE E hs0 hp hnu hL hEcont hE (Aq q) (Aq r)
  have hfb' :
      ‖Cfb (Aq q)-Cfb (Aq r)‖ ≤
        (centerFeedbackLipschitzConstant CE p nu L *
          ((‖B‖/(p-1)) /
            (1-thresholdSelfLipschitzConstant s0 p nu Lc))) *
          ‖q-r‖ := by
    exact hfb.trans
      (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hA
          (centerFeedbackLipschitzConstant_nonneg CE hs0 hp hnu hL))
  have hnl :
      ‖CnlMap q-CnlMap r‖ ≤
        centerNonlinearLipschitzConstant CE p delta Cnl * ‖q-r‖ :=
    weightedCenterNonlinearMap_difference_norm
      CE G hs0 hp hdelta hCnl hGcont hGzero hGlip q r
  have hid :
      fullyCoupledCenterSelfMap B C CE E G
          hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero hGlip
          hLc hCcont hC hself q0 a0 q -
        fullyCoupledCenterSelfMap B C CE E G
          hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero hGlip
          hLc hCcont hC hself q0 a0 r =
      (Cfb (Aq q)-Cfb (Aq r)) + (CnlMap q-CnlMap r) := by
    dsimp [fullyCoupledCenterSelfMap,Aq,Cfb,CnlMap]
    abel
  rw [hid]
  calc
    ‖(Cfb (Aq q)-Cfb (Aq r))+(CnlMap q-CnlMap r)‖
        ≤ ‖Cfb (Aq q)-Cfb (Aq r)‖ + ‖CnlMap q-CnlMap r‖ :=
          norm_add_le _ _
    _ ≤ (centerFeedbackLipschitzConstant CE p nu L *
          ((‖B‖/(p-1)) /
            (1-thresholdSelfLipschitzConstant s0 p nu Lc))) * ‖q-r‖ +
        centerNonlinearLipschitzConstant CE p delta Cnl * ‖q-r‖ :=
          add_le_add hfb' hnl
    _ = fullyCoupledCenterLipschitzConstant
          B CE p nu L delta Cnl Lc * ‖q-r‖ := by
          unfold fullyCoupledCenterLipschitzConstant
          ring

theorem fullyCoupledCenterSelfMap_lipschitz
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl Lc : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L*t^(-nu))
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z-G t w‖ ≤ Cnl*t^(-1-delta)*‖z-w‖)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc*t^(-nu))
    (hself : thresholdSelfLipschitzConstant s0 p nu Lc < 1)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p) :
    LipschitzWith
      (Real.toNNReal
        (fullyCoupledCenterLipschitzConstant B CE p nu L delta Cnl Lc))
      (fullyCoupledCenterSelfMap B C CE E G
        hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero hGlip
        hLc hCcont hC hself q0 a0) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  have hnon := fullyCoupledCenterLipschitzConstant_nonneg
    B CE hs0 hp hnu hL hdelta hCnl hLc hself
  rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ hnon]
  exact fullyCoupledCenterSelfMap_difference_norm
    B C CE E G hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero hGlip
    hLc hCcont hC hself q0 a0 q r

theorem fullyCoupledWeightedBackward_existsUnique
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu L delta Cnl Lc : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L*t^(-nu))
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z-G t w‖ ≤ Cnl*t^(-1-delta)*‖z-w‖)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc*t^(-nu))
    (hself : thresholdSelfLipschitzConstant s0 p nu Lc < 1)
    (q0 : CenterWeightedPath s0 p)
    (a0 : ThresholdWeightedPath s0 p)
    (hfull :
      fullyCoupledCenterLipschitzConstant B CE p nu L delta Cnl Lc < 1) :
    ∃! z : CenterWeightedPath s0 p × ThresholdWeightedPath s0 p,
      z.2 = affineCoupledThresholdMap
        B C hs0 hp hnu hLc hCcont hC a0 z.1 z.2 ∧
      z.1 = q0 +
        weightedCenterFeedbackMap CE E hs0 hp hnu hL hEcont hE z.2 +
        weightedCenterNonlinearMap CE G
          hs0 hp hdelta hCnl hGcont hGzero hGlip z.1 := by
  let Phi := fullyCoupledCenterSelfMap B C CE E G
    hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero hGlip
    hLc hCcont hC hself q0 a0
  have hnon := fullyCoupledCenterLipschitzConstant_nonneg
    B CE hs0 hp hnu hL hdelta hCnl hLc hself
  have hK :
      Real.toNNReal
        (fullyCoupledCenterLipschitzConstant B CE p nu L delta Cnl Lc) <
        (1 : NNReal) :=
    (Real.toNNReal_lt_iff_lt_coe hnon).2 (by simpa using hfull)
  have hPhi : ContractingWith
      (Real.toNNReal
        (fullyCoupledCenterLipschitzConstant B CE p nu L delta Cnl Lc))
      Phi :=
    ⟨hK, fullyCoupledCenterSelfMap_lipschitz
      B C CE E G hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero hGlip
      hLc hCcont hC hself q0 a0⟩
  let qstar : CenterWeightedPath s0 p := hPhi.fixedPoint Phi
  let astar : ThresholdWeightedPath s0 p :=
    coupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 hself qstar
  have hqstar : Phi qstar = qstar := hPhi.fixedPoint_isFixedPt
  have hastar := coupledThresholdMap_fixed
    B C hs0 hp hnu hLc hCcont hC a0 hself qstar
  refine ⟨(qstar,astar), ?_, ?_⟩
  · constructor
    · exact hastar
    · exact hqstar.symm
  · intro z hz
    rcases hz with ⟨hza,hzq⟩
    have haz :
        z.2 =
          coupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 hself z.1 := by
      let huniq := coupledThreshold_existsUnique
        B C hs0 hp hnu hLc hCcont hC a0 z.1 hself
      exact huniq.unique z.2 hza
    have hqfix : Phi z.1 = z.1 := by
      dsimp [Phi,fullyCoupledCenterSelfMap]
      rw [← haz]
      exact hzq.symm
    have hzqstar : z.1=qstar := by
      change z.1=hPhi.fixedPoint Phi
      exact hPhi.fixedPoint_unique hqfix
    apply Prod.ext
    · exact hzqstar
    · rw [haz,hzqstar]
      rfl

#print axioms fullyCoupledCenterSelfMap_difference_norm
#print axioms fullyCoupledWeightedBackward_existsUnique

end HBL.MainBackward
