import HBL.LockedSingleOrbitExponents
import HBL.TypeIIDynamicSelection.ActualHartreeLockedPhysicalGain
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedSpeedTangents
import HBL.TypeIIDynamicSelection.ActualHartreeScaledPhaseSourceTangent
import HBL.TypeIIDynamicSelection.ActualHartreeSelectedKummerRepairGain
import HBL.TypeIIDynamicSelection.ActualKummerRepairTrueBackgroundTimeGain
import HBL.TypeIIDynamicSelection.ActualHartreeRealizedResidualAtlas
import HBL.WeightedThresholdResidualFeedback
import HBL.WeightedJointBackwardResidualLipschitz
import HBL.LockedSingleOrbitBackward
import Mathlib.Tactic

/-!
# Locked single-orbit main-chain audit surface

This module deliberately imports only the shortened route retained for the
final Type-II theorem.  It does NOT import the arbitrary-N finite-profile
recursion or the residual Frechet-derivative route.

The theorem below is only a numerical/positivity interface certificate.  It
does not claim that the physical order-9/4 parametrix has already been
constructed.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.LockedMainChain

open HBL.MainBackward
open HBL.TypeIIDynamicSelection

theorem locked_main_chain_numerical_interface
    (beta rhoStar : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4) :
    0 < actualHartreeLockedKappa beta rhoStar ∧
    1 < lockedSingleOrbitPathWeight ∧
    lockedSingleOrbitPathWeight + 1 < lockedSingleOrbitResidualOrder ∧
    2 < lockedSingleOrbitResidualOrder := by
  exact ⟨
    actual_Hartree_locked_kappa_positive
      beta rhoStar hbeta hrhoStar hflat,
    locked_single_orbit_exponents_admissible.1,
    locked_single_orbit_exponents_admissible.2.1,
    locked_single_orbit_exponents_admissible.2.2⟩

end HBL.LockedMainChain
