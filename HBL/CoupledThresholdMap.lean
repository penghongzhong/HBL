import HBL.WeightedThresholdSelfCoupling
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# Coupled retained-threshold Volterra solve

For each centre path q, solve the exact retained threshold equation
  a = a0 + T_B(q) + T_C(a),
where T_C is the decaying self-coupling from ell E a.

The self-coupling is a strict contraction for sufficiently late s0.
The resulting threshold selector q |-> a(q) is Lipschitz with constant
  K_th / (1 - K_self).
-/

noncomputable section
set_option autoImplicit false

namespace HBL.MainBackward

def affineCoupledThresholdMap
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu Lc : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a0 : ThresholdWeightedPath s0 p)
    (q : CenterWeightedPath s0 p)
    (a : ThresholdWeightedPath s0 p) : ThresholdWeightedPath s0 p :=
  a0 + weightedThresholdMap B s0 p hs0 hp q +
    weightedThresholdSelfMap C hs0 hp hnu hLc hCcont hC a

theorem affineCoupledThresholdMap_difference_norm
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu Lc : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a0 : ThresholdWeightedPath s0 p)
    (q : CenterWeightedPath s0 p)
    (a b : ThresholdWeightedPath s0 p) :
    ‖affineCoupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 q a -
        affineCoupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 q b‖ ≤
      thresholdSelfLipschitzConstant s0 p nu Lc * ‖a-b‖ := by
  have h := weightedThresholdSelfMap_difference_norm
    C hs0 hp hnu hLc hCcont hC a b
  simpa [affineCoupledThresholdMap] using h

theorem affineCoupledThresholdMap_lipschitz
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu Lc : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a0 : ThresholdWeightedPath s0 p)
    (q : CenterWeightedPath s0 p) :
    LipschitzWith
      (Real.toNNReal (thresholdSelfLipschitzConstant s0 p nu Lc))
      (affineCoupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 q) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hnon := thresholdSelfLipschitzConstant_nonneg hs0 hp hnu hLc
  rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ hnon]
  exact affineCoupledThresholdMap_difference_norm
    B C hs0 hp hnu hLc hCcont hC a0 q a b

theorem coupledThreshold_existsUnique
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu Lc : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a0 : ThresholdWeightedPath s0 p)
    (q : CenterWeightedPath s0 p)
    (hsmall : thresholdSelfLipschitzConstant s0 p nu Lc < 1) :
    ∃! a : ThresholdWeightedPath s0 p,
      a = affineCoupledThresholdMap
        B C hs0 hp hnu hLc hCcont hC a0 q a := by
  let K : NNReal :=
    Real.toNNReal (thresholdSelfLipschitzConstant s0 p nu Lc)
  let Phi : ThresholdWeightedPath s0 p → ThresholdWeightedPath s0 p :=
    affineCoupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 q
  have hnon := thresholdSelfLipschitzConstant_nonneg hs0 hp hnu hLc
  have hKlt : K < 1 := by
    dsimp [K]
    exact (Real.toNNReal_lt_iff_lt_coe hnon).2 (by simpa using hsmall)
  have hLip : LipschitzWith K Phi := by
    dsimp [K,Phi]
    exact affineCoupledThresholdMap_lipschitz
      B C hs0 hp hnu hLc hCcont hC a0 q
  have hPhi : ContractingWith K Phi := ⟨hKlt,hLip⟩
  let astar : ThresholdWeightedPath s0 p := hPhi.fixedPoint Phi
  have hfix : Phi astar = astar := hPhi.fixedPoint_isFixedPt
  refine ⟨astar, hfix.symm, ?_⟩
  intro a ha
  change a = astar
  apply hPhi.fixedPoint_unique
  change Phi a = a
  exact ha.symm

noncomputable def coupledThresholdMap
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu Lc : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a0 : ThresholdWeightedPath s0 p)
    (hsmall : thresholdSelfLipschitzConstant s0 p nu Lc < 1)
    (q : CenterWeightedPath s0 p) : ThresholdWeightedPath s0 p :=
  Classical.choose
    (ExistsUnique.exists
      (coupledThreshold_existsUnique
        B C hs0 hp hnu hLc hCcont hC a0 q hsmall))

theorem coupledThresholdMap_fixed
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu Lc : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a0 : ThresholdWeightedPath s0 p)
    (hsmall : thresholdSelfLipschitzConstant s0 p nu Lc < 1)
    (q : CenterWeightedPath s0 p) :
    coupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 hsmall q =
      affineCoupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 q
        (coupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 hsmall q) := by
  exact Classical.choose_spec
    (ExistsUnique.exists
      (coupledThreshold_existsUnique
        B C hs0 hp hnu hLc hCcont hC a0 q hsmall))

theorem coupledThresholdMap_difference_norm
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu Lc : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a0 : ThresholdWeightedPath s0 p)
    (hsmall : thresholdSelfLipschitzConstant s0 p nu Lc < 1)
    (q r : CenterWeightedPath s0 p) :
    ‖coupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 hsmall q -
        coupledThresholdMap B C hs0 hp hnu hLc hCcont hC a0 hsmall r‖ ≤
      ((‖B‖ / (p-1)) /
        (1 - thresholdSelfLipschitzConstant s0 p nu Lc)) * ‖q-r‖ := by
  let aq := coupledThresholdMap
    B C hs0 hp hnu hLc hCcont hC a0 hsmall q
  let ar := coupledThresholdMap
    B C hs0 hp hnu hLc hCcont hC a0 hsmall r
  let Tq := weightedThresholdMap B s0 p hs0 hp
  let S := weightedThresholdSelfMap C hs0 hp hnu hLc hCcont hC
  have hqfix := coupledThresholdMap_fixed
    B C hs0 hp hnu hLc hCcont hC a0 hsmall q
  have hrfix := coupledThresholdMap_fixed
    B C hs0 hp hnu hLc hCcont hC a0 hsmall r
  have hsplit :
      aq-ar = (Tq q-Tq r) + (S aq-S ar) := by
    dsimp [aq,ar,Tq,S,affineCoupledThresholdMap] at hqfix hrfix ⊢
    rw [hqfix,hrfix]
    abel
  have hT :
      ‖Tq q-Tq r‖ ≤ (‖B‖/(p-1))*‖q-r‖ := by
    dsimp [Tq]
    exact weightedThresholdMap_difference_norm B s0 p hs0 hp q r
  have hS :
      ‖S aq-S ar‖ ≤
        thresholdSelfLipschitzConstant s0 p nu Lc * ‖aq-ar‖ := by
    dsimp [S]
    exact weightedThresholdSelfMap_difference_norm
      C hs0 hp hnu hLc hCcont hC aq ar
  have hsum :
      ‖aq-ar‖ ≤
        (‖B‖/(p-1))*‖q-r‖ +
          thresholdSelfLipschitzConstant s0 p nu Lc * ‖aq-ar‖ := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hT hS)
  have hpos :
      0 < 1 - thresholdSelfLipschitzConstant s0 p nu Lc :=
    sub_pos.mpr hsmall
  have hlin :
      ‖aq-ar‖ * (1 - thresholdSelfLipschitzConstant s0 p nu Lc) ≤
        (‖B‖/(p-1))*‖q-r‖ := by
    nlinarith
  change ‖aq-ar‖ ≤ _
  calc
    ‖aq-ar‖ ≤ ((‖B‖/(p-1))*‖q-r‖) /
        (1-thresholdSelfLipschitzConstant s0 p nu Lc) :=
      (le_div_iff₀ hpos).2 hlin
    _ = ((‖B‖/(p-1)) /
        (1-thresholdSelfLipschitzConstant s0 p nu Lc))*‖q-r‖ := by ring

theorem coupledThresholdMap_lipschitz
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (C : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    {s0 p nu Lc : ℝ}
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hLc : 0 ≤ Lc) (hCcont : Continuous C)
    (hC : ∀ t, s0 ≤ t → ‖C t‖ ≤ Lc * t ^ (-nu))
    (a0 : ThresholdWeightedPath s0 p)
    (hsmall : thresholdSelfLipschitzConstant s0 p nu Lc < 1) :
    LipschitzWith
      (Real.toNNReal
        ((‖B‖/(p-1)) /
          (1-thresholdSelfLipschitzConstant s0 p nu Lc)))
      (coupledThresholdMap
        B C hs0 hp hnu hLc hCcont hC a0 hsmall) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  have hnum : 0 ≤ ‖B‖/(p-1) := by positivity
  have hden : 0 < 1-thresholdSelfLipschitzConstant s0 p nu Lc :=
    sub_pos.mpr hsmall
  have hnon :
      0 ≤ (‖B‖/(p-1)) /
        (1-thresholdSelfLipschitzConstant s0 p nu Lc) :=
    div_nonneg hnum hden.le
  rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ hnon]
  exact coupledThresholdMap_difference_norm
    B C hs0 hp hnu hLc hCcont hC a0 hsmall q r

#print axioms coupledThreshold_existsUnique
#print axioms coupledThresholdMap_difference_norm
#print axioms coupledThresholdMap_lipschitz

end HBL.MainBackward
