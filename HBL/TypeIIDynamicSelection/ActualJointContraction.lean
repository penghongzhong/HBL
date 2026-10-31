import HBL.WeightedJointBackward
import Mathlib.Tactic

/-!
# Candidate revised manuscript 5.2: actual weighted joint ball contraction

This terminal concerns the genuine HBL constrained centre and retained
two-dimensional threshold weighted path spaces. It strengthens the existing
global fixed-point result by deriving invariance of the prescribed closed
ball from the source at zero and its proved Lipschitz coefficient. No
self-map condition is assumed.

It does NOT identify the input E and G with the complete physical Hartree
geometric/nonlinear source, or construct the original common-domain
propagator. Hence it must not be counted as a newly accepted complete
original manuscript 5.2 or as proof of Type II blowup.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.MainBackward

/-- One *actual* HBL weighted centre/threshold map contracts its specified
closed ball, and its unique simultaneous fixed point lies in that ball.
The nontrivial forcing smallness is a direct estimate of the same map at
zero, rather than an assumption of invariance or a fixed point. -/
theorem actual_weighted_joint_ball_contraction
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
    (r : ℝ) (hr : 0 ≤ r)
    (hsmall : weightedJointLipschitzConstant B CE p nu L delta Cnl < 1)
    (hforcing :
      ‖fullWeightedCenterSelfMap B CE E G
        hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero
        hGlip q0 a0 0‖ ≤
        (1 - weightedJointLipschitzConstant B CE p nu L delta Cnl) * r) :
    (∀ q : CenterWeightedPath s0 p, ‖q‖ ≤ r →
      ‖fullWeightedCenterSelfMap B CE E G
        hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero
        hGlip q0 a0 q‖ ≤ r) ∧
    (∃! z : CenterWeightedPath s0 p × ThresholdWeightedPath s0 p,
      ‖z.1‖ ≤ r ∧
      z.2 = affineWeightedThresholdMap B s0 p hs0 hp a0 z.1 ∧
      z.1 = fullWeightedCenterSelfMap B CE E G
        hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero
        hGlip q0 a0 z.1) := by
  let k : ℝ := weightedJointLipschitzConstant B CE p nu L delta Cnl
  let Phi := fullWeightedCenterSelfMap B CE E G
    hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero
    hGlip q0 a0
  have hk : 0 ≤ k :=
    weightedJointLipschitzConstant_nonneg B CE hs0 hp hnu hL hdelta hCnl
  have hklt : k < 1 := hsmall
  have hz : ‖Phi 0‖ ≤ (1 - k) * r := hforcing
  have hdiff (q : CenterWeightedPath s0 p) :
      ‖Phi q - Phi 0‖ ≤ k * ‖q‖ := by
    have ht := fullWeightedCenterSelfMap_difference_norm
      B CE E G hs0 hp hnu hL hEcont hE hdelta hCnl hGcont
      hGzero hGlip q0 a0 q 0
    change ‖Phi q - Phi 0‖ ≤ k * ‖q - 0‖ at ht
    simpa only [sub_zero] using ht
  have hbound (q : CenterWeightedPath s0 p) :
      ‖Phi q‖ ≤ k * ‖q‖ + ‖Phi 0‖ := by
    calc
      ‖Phi q‖ = ‖(Phi q - Phi 0) + Phi 0‖ := by
        congr 1
        abel
      _ ≤ ‖Phi q - Phi 0‖ + ‖Phi 0‖ := norm_add_le _ _
      _ ≤ k * ‖q‖ + ‖Phi 0‖ := add_le_add_right (hdiff q) _
  have hball (q : CenterWeightedPath s0 p) (hq : ‖q‖ ≤ r) :
      ‖Phi q‖ ≤ r := by
    calc
      ‖Phi q‖ ≤ k * ‖q‖ + ‖Phi 0‖ := hbound q
      _ ≤ k * r + (1-k) * r :=
        add_le_add (mul_le_mul_of_nonneg_left hq hk) hz
      _ = r := by ring
  refine ⟨hball, ?_⟩
  obtain ⟨z, hfix, hunique⟩ :=
    nonlinear_weighted_joint_backward_fixed_point B CE E G
      hs0 hp hnu hL hEcont hE hdelta hCnl hGcont hGzero
      hGlip q0 a0 hsmall
  have hcentre : z.1 = Phi z.1 := hfix.2
  have hineq : ‖z.1‖ ≤ k * ‖z.1‖ + (1-k) * r := by
    calc
      ‖z.1‖ = ‖Phi z.1‖ := congrArg norm hcentre
      _ ≤ k * ‖z.1‖ + ‖Phi 0‖ := hbound z.1
      _ ≤ k * ‖z.1‖ + (1-k)*r := add_le_add_left hz _
  have hgap : 0 < 1-k := by linarith
  have hineq' : (1-k) * ‖z.1‖ ≤ (1-k)*r := by
    nlinarith only [hineq]
  have hnorm : ‖z.1‖ ≤ r := (mul_le_mul_left hgap).mp hineq'
  refine ⟨z, ⟨hnorm, hfix.1, hfix.2⟩, ?_⟩
  intro y hy
  exact hunique y ⟨hy.2.1, hy.2.2⟩

end HBL.TypeIIDynamicSelection
