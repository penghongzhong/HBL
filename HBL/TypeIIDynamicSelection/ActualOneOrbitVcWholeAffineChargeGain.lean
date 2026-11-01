import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeWeightedFredholm
import HBL.ActualInnerAffinelyCorrected
import Mathlib.Tactic

/-!
# Quantitative affine charges of the genuine full mixed Hartree density

This applies the already proved exact L¹ estimate for
F_ell = |V_c + Z_ell|^4 - |V_c|^4 - |Z_ell|^4
to the *actual* H+ and H- resonance functionals, not surrogate charges.
In particular, their unique affine corrections gain a positive half order
relative to the slow monopole mass, at the chosen real annular datum.

These are physical density contributions to threshold charges. They are
NOT the whole projected time-dependent PDE sources, and this is not the
original manuscript environment 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.AffineTail
open HBL.Profile.ActualInner

/-- The exact Hartree mixed quartic density has a small pairing with
either of the two physical zero-energy resonances. The bound follows from
the original L¹ estimate, not an assumed pairing estimate. -/
theorem actual_one_orbit_Vc_whole_mixed_threshold_pairing_gain
    (ell : ℝ) (hell : 0 < ell) (ch : HartreeChannel) :
    |channelPairing ch (actualOneOrbitVcWholeMixedQuartic ell)| ≤
      actualOneOrbitVcWholeMixedL1Envelope ell := by
  let F : ℝ → ℝ := actualOneOrbitVcWholeMixedQuartic ell
  have hsource :=
    actual_one_orbit_Vc_whole_mixed_Hartree_L1_center_gain ell hell
  have hWF : InWeightedL2 (7 / 4 : ℝ) F :=
    actual_one_orbit_Vc_whole_mixed_in_real_weighted_Fredholm
      ell (7 / 4) hell
  have hPairInt :
      IntegrableOn (fun r : ℝ => channelResonance ch r * F r)
        (Ioi (0 : ℝ)) :=
    channel_data_pairing_integrableOn ch (7 / 4) (by norm_num) F hWF
  have hPairAbsInt :
      IntegrableOn (fun r : ℝ => |channelResonance ch r * F r|)
        (Ioi (0 : ℝ)) := hPairInt.abs
  have hFAbsInt :
      IntegrableOn (fun r : ℝ => |F r|) (Ioi (0 : ℝ)) :=
    hsource.1.abs.integrableOn
  have hpoint :
      ∀ᵐ r : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
        |channelResonance ch r * F r| ≤ |F r| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [abs_mul]
    calc
      |channelResonance ch r| * |F r| ≤ 1 * |F r| :=
        mul_le_mul_of_nonneg_right
          (channelResonance_abs_le_one ch r hr.le) (abs_nonneg _)
      _ = |F r| := one_mul _
  change |∫ r in Ioi (0 : ℝ),
    channelResonance ch r * F r| ≤
      actualOneOrbitVcWholeMixedL1Envelope ell
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), |channelResonance ch r * F r| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ r in Ioi (0 : ℝ), |F r| :=
      integral_mono_ae hPairAbsInt hFAbsInt hpoint
    _ ≤ actualOneOrbitVcWholeMixedL1Envelope ell := hsource.2.1

/-- The genuine plus-channel affine correction coefficient is O(L¹ mass). -/
theorem actual_one_orbit_Vc_whole_mixed_plus_affine_charge_gain
    (ell : ℝ) (hell : 0 < ell) :
    |actualPlusCharge (actualOneOrbitVcWholeMixedQuartic ell)| ≤
      2 * actualOneOrbitVcWholeMixedL1Envelope ell := by
  have hpair :=
    actual_one_orbit_Vc_whole_mixed_threshold_pairing_gain
      ell hell HartreeChannel.plus
  have hformula :
      actualPlusCharge (actualOneOrbitVcWholeMixedQuartic ell) =
        2 * channelPairing HartreeChannel.plus
          (actualOneOrbitVcWholeMixedQuartic ell) := by
    simp [actualPlusCharge, channelLimit]
    ring
  rw [hformula, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left hpair (by norm_num)

/-- The genuine minus-channel affine correction coefficient has the
same L¹-size as its resonant source pairing. -/
theorem actual_one_orbit_Vc_whole_mixed_minus_affine_charge_gain
    (ell : ℝ) (hell : 0 < ell) :
    |actualMinusCharge (actualOneOrbitVcWholeMixedQuartic ell)| ≤
      actualOneOrbitVcWholeMixedL1Envelope ell := by
  have hpair :=
    actual_one_orbit_Vc_whole_mixed_threshold_pairing_gain
      ell hell HartreeChannel.minus
  simpa [actualMinusCharge, channelLimit] using hpair

end HBL.TypeIIDynamicSelection
