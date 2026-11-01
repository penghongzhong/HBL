import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeAffineChargeGain
import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeMixedPositiveHalf
import HBL.ActualInnerAffinelyCorrected
import Mathlib.Tactic

/-!
# Actual Hartree mixed quartic: positive half-order Fredholm charges

For the explicit *one-orbit terminal datum*, the genuine physical
mixed quartic density F_ell has an actual Hartree L1 mass
O(ell^(3/2)). Reuse the exact two channel resonances to obtain
quantitative, *not assumed*, affine charge bounds. The corrected
sources are compatible in the real H+ and H- weighted Fredholm spaces.

These are terminal-density components. Neither projected entire
renormalized PDE channel forcing nor the off-terminal matched
one-layer equation is replaced by these assertions.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology RealInnerProductSpace

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.AffineTail
open HBL.Modulation.Monopole
open HBL.Profile.ActualInner HBL.L2Kernel

/-- Both actual zero-energy Hartree resonances gain a positive half
order on the physical mixed density at the chosen terminal orbit. -/
theorem actual_one_orbit_Vc_whole_mixed_threshold_pairing_half_order
    (ell : ℝ) (hell : 0 < ell) (hsmall : ell ≤ 1)
    (ch : HartreeChannel) :
    |channelPairing ch (actualOneOrbitVcWholeMixedQuartic ell)| ≤
      actualOneOrbitVcWholeMixedHalfOrderCoefficient *
        ell * Real.sqrt ell := by
  exact
    (actual_one_orbit_Vc_whole_mixed_threshold_pairing_gain ell hell ch).trans
      (actual_one_orbit_Vc_whole_mixed_envelope_half_order
        ell hell hsmall)

/-- The two *uniquely determined* real affine charges, with the
explicit 1/2-order improvement beyond the O(ell) slow monopole. -/
theorem actual_one_orbit_Vc_whole_mixed_affine_charges_half_order
    (ell : ℝ) (hell : 0 < ell) (hsmall : ell ≤ 1) :
    |actualPlusCharge (actualOneOrbitVcWholeMixedQuartic ell)| ≤
      (2 * actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
        ell * Real.sqrt ell ∧
    |actualMinusCharge (actualOneOrbitVcWholeMixedQuartic ell)| ≤
      actualOneOrbitVcWholeMixedHalfOrderCoefficient *
        ell * Real.sqrt ell := by
  have hEnvelope :=
    actual_one_orbit_Vc_whole_mixed_envelope_half_order
      ell hell hsmall
  constructor
  · calc
      |actualPlusCharge (actualOneOrbitVcWholeMixedQuartic ell)| ≤
          2 * actualOneOrbitVcWholeMixedL1Envelope ell :=
        actual_one_orbit_Vc_whole_mixed_plus_affine_charge_gain ell hell
      _ ≤ 2 * (actualOneOrbitVcWholeMixedHalfOrderCoefficient *
            ell * Real.sqrt ell) :=
        mul_le_mul_of_nonneg_left hEnvelope (by norm_num)
      _ = (2 * actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
            ell * Real.sqrt ell := by ring
  · exact
      (actual_one_orbit_Vc_whole_mixed_minus_affine_charge_gain ell hell).trans
        hEnvelope

/-- The real mixed physical density, after its *forced* affine
charges are subtracted, lies in BOTH original weighted spaces with
both true resonance pairings identically zero. -/
theorem actual_one_orbit_Vc_whole_mixed_both_corrected_sources
    (ell sigma : ℝ) (hell : 0 < ell)
    (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) :
    InWeightedL2 sigma
        (correctedPlusSource (actualOneOrbitVcWholeMixedQuartic ell)) ∧
    InWeightedL2 sigma
        (correctedMinusSource (actualOneOrbitVcWholeMixedQuartic ell)) ∧
    channelPairing HartreeChannel.plus
        (correctedPlusSource (actualOneOrbitVcWholeMixedQuartic ell)) = 0 ∧
    channelPairing HartreeChannel.minus
        (correctedMinusSource (actualOneOrbitVcWholeMixedQuartic ell)) = 0 := by
  let F := actualOneOrbitVcWholeMixedQuartic ell
  have hF : InWeightedL2 sigma F :=
    actual_one_orbit_Vc_whole_mixed_in_real_weighted_Fredholm
      ell sigma hell
  have hCompat :=
    actualAffine_corrected_sources_compatible sigma (by linarith)
      F F hF hF
  exact ⟨correctedPlusSource_memWeightedL2 sigma hUpper.le F hF,
    correctedMinusSource_memWeightedL2 sigma hUpper.le F hF,
    hCompat.1, hCompat.2⟩

end HBL.TypeIIDynamicSelection
