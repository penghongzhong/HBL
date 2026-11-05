import HBL.TypeIIDynamicSelection.ActualHartreeCorrectionResidualAtom
import HBL.TypeIIDynamicSelection.ActualHartreeCutoffResidualAtom
import HBL.TypeIIDynamicSelection.ActualHartreeFlatResidualAtom
import HBL.TypeIIDynamicSelection.ActualHartreeParameterResidualAtom
import HBL.TypeIIDynamicSelection.ActualHartreeSlowCenterResidualAtom
import HBL.TypeIIDynamicSelection.ActualHartreeKummerRepairResidualAtom
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalOneLayerGain
import Mathlib.Tactic

/-!
# Uniform physical gain floor for the realized HBL residual atoms

All six imports above are concrete residual producers.  Their norm bounds
are proved in their own files from the actual Hartree/Kummer expressions;
this file does not replace those bounds by an order tag.

The purpose here is only to identify a single strictly positive floor
kappa_phys which is below the four base physical gains, while the actual
correction and Kummer-repair remainders already occur at rho+kappa_phys.

This is a main-chain bookkeeping bridge to the finite residual ledger, not
yet the construction of every recursive profile packet.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

open HBL.Profile.OneLayer

/-- The concrete realized atom orders admit the same positive physical floor.
The first four inequalities correspond respectively to the realized cutoff,
parameter, flat-radiation and slow-center atoms.  The final two identities
are the actual correction remainder and physical Kummer-repair atom orders. -/
theorem actual_Hartree_realized_atom_orders_uniform_floor
    (beta rhoStar rho : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4) :
    let kappa := actualHartreePhysicalKappa beta rhoStar
    0 < kappa ∧
    1 + kappa ≤ 1 + actualHartreeFullShellTimeGain beta ∧
    1 + kappa ≤ 1 + actualMonopoleParameterGain beta ∧
    1 + kappa ≤ 1 + actualHartreeFlatGain beta rhoStar ∧
    1 + kappa ≤ 2 * beta ∧
    rho + kappa = rho + actualHartreePhysicalKappa beta rhoStar ∧
    rho + kappa = rho + actualHartreePhysicalKappa beta rhoStar := by
  dsimp only
  let kappa := actualHartreePhysicalKappa beta rhoStar
  have hk : 0 < kappa := by
    dsimp [kappa]
    exact actual_Hartree_physical_kappa_positive
      beta rhoStar hbeta hrhoStar hflat
  have hcut :
      kappa ≤ actualHartreeFullShellTimeGain beta := by
    simpa only [kappa, actualHartreePhysicalGain] using
      actual_Hartree_physical_kappa_le_gain
        beta rhoStar GainCause.cutoff
  have hparam :
      kappa ≤ actualMonopoleParameterGain beta := by
    simpa only [kappa, actualHartreePhysicalGain] using
      actual_Hartree_physical_kappa_le_gain
        beta rhoStar GainCause.parameter
  have hflatGain :
      kappa ≤ actualHartreeFlatGain beta rhoStar := by
    simpa only [kappa, actualHartreePhysicalGain] using
      actual_Hartree_physical_kappa_le_gain
        beta rhoStar GainCause.flatRadiation
  have hslow :
      kappa ≤ 2 * beta - 1 := by
    simpa only [kappa, actualHartreePhysicalGain] using
      actual_Hartree_physical_kappa_le_gain
        beta rhoStar GainCause.slowMonopole
  refine ⟨hk, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rfl
  · rfl

end HBL.TypeIIDynamicSelection
