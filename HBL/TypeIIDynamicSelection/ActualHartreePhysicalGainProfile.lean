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
    (hbeta : 1 / 2 < beta)
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

/-- Every structural gain is bounded by the corresponding already-derived
physical exponent (or equals the Frobenius half-order).  In particular the
minimum gain used by finite recursion is a genuine PDE-derived positive
quantity, not an assigned order label. -/
theorem actual_Hartree_structural_gains_have_physical_producers
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

/-- The actual profile gain is below all four quantitative physical gains
and the fixed Frobenius half-order.  This is the precise exponent interface
needed when actual residual atoms are attached to the structural recursion. -/
theorem actual_Hartree_kappa_profile_below_physical_gains
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
  have hprod := actual_Hartree_structural_gains_have_physical_producers
    beta rho hbeta hrho hflat
  dsimp only at hprod
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (kappaProfile_le_gain P GainCause.cutoff).trans hprod.1
  · simpa [hprod.2] using kappaProfile_le_gain P GainCause.parameter
  · simpa [hprod.2.2.1] using kappaProfile_le_gain P GainCause.flatRadiation
  · simpa [hprod.2.2.2.1] using kappaProfile_le_gain P GainCause.slowMonopole
  · simpa [hprod.2.2.2.2] using kappaProfile_le_gain P GainCause.frobenius

end HBL.TypeIIDynamicSelection
