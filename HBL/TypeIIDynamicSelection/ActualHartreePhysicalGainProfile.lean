import HBL.OneLayerElimination
import HBL.TypeIIDynamicSelection.ActualHartreeOneOrbitFullShellTimeGain
import HBL.TypeIIDynamicSelection.ActualMonopoleParameterSpeedGain
import HBL.TypeIIDynamicSelection.ActualFlatGainIntegrability
import HBL.TypeIIDynamicSelection.ActualWholeRadiationCenterReduction
import Mathlib.Tactic

/-!
# Physical realization of the one-layer gain parameters

The structural finite-profile recursion uses five gain mechanisms.  This file
removes the freedom to assign arbitrary positive gain exponents: the cutoff,
parameter, flat-radiation and slow-monopole exponents are instantiated by
quantities already derived from the actual Hartree PDE estimates.

This is an exponent bridge only.  It does not classify every new PDE residual
atom by a gain cause; that source-level classification remains the next
closure obligation.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

open HBL.Profile.OneLayer

def actualHartreePhysicalGainParameters
    (beta rho : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4) :
    GainParameters where
  delta := actualMonopoleParameterGain beta
  epsFlat := actualHartreeFlatGain beta rho
  betaMinus := beta
  rhoStar := rho
  delta_pos := actual_monopole_parameter_gain_positive beta hbeta
  epsFlat_pos := actual_Hartree_flat_gain_strict_pos beta rho hbeta hrho hflat
  beta_half := hbeta
  rhoStar_pos := hrho

theorem actual_Hartree_cutoff_gain_dominates_structural_rho
    (beta rho : ℝ)
    (_hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4) :
    rho < actualHartreeFullShellTimeGain beta := by
  have hright : 0 < (5 * beta - 2) / 4 := by
    linarith
  unfold actualHartreeFullShellTimeGain
  linarith

theorem actual_Hartree_physical_gain_profile_positive
    (beta rho : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4) :
    0 < kappaProfile
      (actualHartreePhysicalGainParameters beta rho hbeta hrho hflat) :=
  kappaProfile_pos _

/-- Four structural gains are bounded by corresponding already-derived
physical exponents.  The Frobenius entry is recorded only as the structural
half-order and is NOT claimed here to be physically realized by the current
Kummer residual. -/
theorem actual_Hartree_four_structural_gains_have_physical_producers
    (beta rho : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4) :
    let P := actualHartreePhysicalGainParameters beta rho hbeta hrho hflat
    gain P GainCause.cutoff ≤ actualHartreeFullShellTimeGain beta ∧
    gain P GainCause.parameter = actualMonopoleParameterGain beta ∧
    gain P GainCause.flatRadiation = actualHartreeFlatGain beta rho ∧
    gain P GainCause.slowMonopole = 2 * beta - 1 ∧
    gain P GainCause.frobenius = 1 / 2 := by
  dsimp [actualHartreePhysicalGainParameters, gain]
  exact ⟨(actual_Hartree_cutoff_gain_dominates_structural_rho
      beta rho hbeta hrho hflat).le, rfl, rfl, rfl, rfl⟩

/-- The profile minimum lies below the four quantitative physical gains.
The final half-order inequality is only the structural Frobenius ceiling;
a separate same-source Frobenius residual bridge is still required. -/
theorem actual_Hartree_kappa_profile_below_four_physical_gains
    (beta rho : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4) :
    let P := actualHartreePhysicalGainParameters beta rho hbeta hrho hflat
    kappaProfile P ≤ actualHartreeFullShellTimeGain beta ∧
    kappaProfile P ≤ actualMonopoleParameterGain beta ∧
    kappaProfile P ≤ actualHartreeFlatGain beta rho ∧
    kappaProfile P ≤ 2 * beta - 1 ∧
    kappaProfile P ≤ 1 / 2 := by
  dsimp only
  let P := actualHartreePhysicalGainParameters beta rho hbeta hrho hflat
  have hprod := actual_Hartree_four_structural_gains_have_physical_producers
    beta rho hbeta hrho hflat
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (kappaProfile_le_gain P GainCause.cutoff).trans hprod.1
  · simpa [P, gain, actualHartreePhysicalGainParameters] using
      (kappaProfile_le_gain P GainCause.parameter)
  · simpa [P, gain, actualHartreePhysicalGainParameters] using
      (kappaProfile_le_gain P GainCause.flatRadiation)
  · simpa [P, gain, actualHartreePhysicalGainParameters] using
      (kappaProfile_le_gain P GainCause.slowMonopole)
  · simpa [P, gain, actualHartreePhysicalGainParameters] using
      (kappaProfile_le_gain P GainCause.frobenius)

end HBL.TypeIIDynamicSelection
