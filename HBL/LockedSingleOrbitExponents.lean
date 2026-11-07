import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Locked exponents for the shortened single-orbit HBL construction

The final Type-II theorem only needs one backward fixed point.  We therefore
fix one path weight and one residual order instead of carrying an arbitrary
profile order N through the construction.

  p_* = 9/8,
  N_* = nu_* = 9/4.

These satisfy exactly the three downstream inequalities:
  1 < p_*,
  p_* + 1 < N_*,
  2 < nu_*.

The last theorem converts an O(s^{-N_*}) source to the slightly weaker
O(s^{-p_*-1}) threshold-forcing bound for s>=1.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.MainBackward

def lockedSingleOrbitPathWeight : ℝ := 9 / 8

def lockedSingleOrbitResidualOrder : ℝ := 9 / 4

theorem locked_single_orbit_exponents_admissible :
    1 < lockedSingleOrbitPathWeight ∧
    lockedSingleOrbitPathWeight + 1 < lockedSingleOrbitResidualOrder ∧
    2 < lockedSingleOrbitResidualOrder := by
  norm_num [lockedSingleOrbitPathWeight, lockedSingleOrbitResidualOrder]

theorem locked_single_orbit_residual_implies_threshold_power
    (s : ℝ) (hs : 1 ≤ s) :
    s ^ (-lockedSingleOrbitResidualOrder) ≤
      s ^ (-lockedSingleOrbitPathWeight - 1) := by
  apply Real.rpow_le_rpow_of_exponent_le hs
  norm_num [lockedSingleOrbitPathWeight, lockedSingleOrbitResidualOrder]

theorem locked_single_orbit_residual_bound_implies_threshold_bound
    (s C x : ℝ) (hs : 1 ≤ s) (hC : 0 ≤ C)
    (hx : |x| ≤ C * s ^ (-lockedSingleOrbitResidualOrder)) :
    |x| ≤ C * s ^ (-lockedSingleOrbitPathWeight - 1) := by
  exact hx.trans
    (mul_le_mul_of_nonneg_left
      (locked_single_orbit_residual_implies_threshold_power s hs) hC)

end HBL.MainBackward
