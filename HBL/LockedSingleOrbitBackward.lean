import HBL.LockedSingleOrbitExponents
import HBL.WeightedAffineForcing
import HBL.WeightedJointBackwardResidualLipschitz
import Mathlib.Tactic

/-!
# Locked order-9/4 parametrix feeds the final backward fixed point

This is the downstream consumer proving that the shortened §2.13 target is
sufficient.  Given:
* actual threshold and center affine forcing of order 9/4;
* a direct threshold-residual difference bound of order 9/4;
* the already retained nonlinear center Lipschitz term;

we construct the fixed affine paths a0,q0 with the locked path weight 9/8
and invoke the direct residual-Lipschitz joint Banach theorem.

No arbitrary profile order N and no residual Frechet derivative occur.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace HBL.MainBackward

theorem locked_single_orbit_order_nine_fourths_backward_fixed_point
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    {s0 Cth Cc L delta Cnl : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (Fth : ℝ → ℝ × ℝ)
    (Fc : ℝ → ConstrainedCenterSpace)
    (H : ℝ → (ℝ × ℝ) → ConstrainedCenterSpace)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 1 ≤ s0)
    (hCth : 0 ≤ Cth) (hCc : 0 ≤ Cc) (hL : 0 ≤ L)
    (hFthCont : Continuous Fth)
    (hFcCont : Continuous Fc)
    (hFth : ∀ t : ℝ, s0 ≤ t →
      ‖Fth t‖ ≤ Cth * t ^ (-lockedSingleOrbitResidualOrder))
    (hFc : ∀ t : ℝ, s0 ≤ t →
      ‖Fc t‖ ≤ Cc * t ^ (-lockedSingleOrbitResidualOrder))
    (hHcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2))
    (hHzero : ∀ t, s0 ≤ t → H t 0 = 0)
    (hHlip : ∀ t, s0 ≤ t → ∀ theta eta,
      ‖H t theta - H t eta‖ ≤
        L * t ^ (-lockedSingleOrbitResidualOrder) * ‖theta - eta‖)
    (hdelta : 0 < delta) (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous
      (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤
        Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (hsmall :
      weightedJointLipschitzConstant B CE
        lockedSingleOrbitPathWeight lockedSingleOrbitResidualOrder
        L delta Cnl < 1) :
    let a0 : ThresholdWeightedPath s0 lockedSingleOrbitPathWeight :=
      weightedThresholdForcingPath
        Fth s0 lockedSingleOrbitPathWeight Cth
        (lt_of_lt_of_le zero_lt_one hs0)
        locked_single_orbit_exponents_admissible.1
        hCth hFthCont
        (fun t ht => by
          exact (hFth t ht).trans
            (mul_le_mul_of_nonneg_left
              (locked_single_orbit_residual_implies_threshold_power
                t (hs0.le.trans ht))
              hCth))
    let q0 : CenterWeightedPath s0 lockedSingleOrbitPathWeight :=
      weightedCenterForcingPath
        CE Fc lockedSingleOrbitPathWeight lockedSingleOrbitResidualOrder Cc
        (lt_of_lt_of_le zero_lt_one hs0)
        locked_single_orbit_exponents_admissible.1
        locked_single_orbit_exponents_admissible.2.1
        hCc hFcCont hFc
    ∃! z :
        CenterWeightedPath s0 lockedSingleOrbitPathWeight ×
          ThresholdWeightedPath s0 lockedSingleOrbitPathWeight,
      z.2 = affineWeightedThresholdMap
        B s0 lockedSingleOrbitPathWeight
          (lt_of_lt_of_le zero_lt_one hs0)
          locked_single_orbit_exponents_admissible.1 a0 z.1 ∧
      z.1 =
        fullWeightedCenterResidualLipschitzSelfMap
          B CE H G (lt_of_lt_of_le zero_lt_one hs0)
            locked_single_orbit_exponents_admissible.1
            locked_single_orbit_exponents_admissible.2.2
            hL hHcont hHzero hHlip
            hdelta hCnl hGcont hGzero hGlip q0 a0 z.1 := by
  dsimp only
  have hs0pos : 0 < s0 := lt_of_lt_of_le zero_lt_one hs0
  have hp : 1 < lockedSingleOrbitPathWeight :=
    locked_single_orbit_exponents_admissible.1
  have hN :
      lockedSingleOrbitPathWeight + 1 <
        lockedSingleOrbitResidualOrder :=
    locked_single_orbit_exponents_admissible.2.1
  have hnu : 2 < lockedSingleOrbitResidualOrder :=
    locked_single_orbit_exponents_admissible.2.2
  have hFthWeak :
      ∀ t : ℝ, s0 ≤ t →
        ‖Fth t‖ ≤
          Cth * t ^ (-lockedSingleOrbitPathWeight - 1) := by
    intro t ht
    have ht1 : 1 ≤ t := by
      exact hs0.trans ht
    exact (hFth t ht).trans
      (mul_le_mul_of_nonneg_left
        (locked_single_orbit_residual_implies_threshold_power t ht1) hCth)
  let a0 : ThresholdWeightedPath s0 lockedSingleOrbitPathWeight :=
    weightedThresholdForcingPath
      Fth s0 lockedSingleOrbitPathWeight Cth
      hs0pos hp hCth hFthCont hFthWeak
  let q0 : CenterWeightedPath s0 lockedSingleOrbitPathWeight :=
    weightedCenterForcingPath
      CE Fc lockedSingleOrbitPathWeight lockedSingleOrbitResidualOrder Cc
      hs0pos hp hN hCc hFcCont hFc
  exact nonlinear_weighted_joint_backward_fixed_point_residual_lipschitz
    B CE H G hs0pos hp hnu hL hHcont hHzero hHlip
      hdelta hCnl hGcont hGzero hGlip q0 a0 hsmall

end HBL.MainBackward
