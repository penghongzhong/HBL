import HBL.TypeIIDynamicSelection.ActualHartreePhysicalInnerFredholm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Physical affine charges retain the actual one-eighth length gain

The two affine slopes in the real inner inverse are not free parameters.
Their exact resonance integrals are bounded using the already proved
complete Hartree source. We derive an integrable (1+r)^(-19/8) envelope,
then bound the two actual resonance pairings. No source order, charge
size, time law or boundary matching datum is assumed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- A fixed Lebesgue integral, independent of all physical parameters. -/
def actualHartreePhysicalChargeTailIntegral : ℝ :=
  ∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(19 / 8 : ℝ))

/-- The full source, not a single component, has an integrable radial
majorant after removing the original positive Fredholm weight. -/
theorem actual_Hartree_physical_source_unweighted_pointwise
    (B A ell c r : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hr : 0 < r) (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    ‖actualHartreePhysicalSliceInteraction ell c z r‖ ≤
      actualHartreePhysicalWeightedSourceConstant B A *
        ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(19 / 8 : ℝ)) := by
  have hd : 0 < 1 + r := by linarith
  have hw : 0 < (1 + r) ^ (7 / 4 : ℝ) := Real.rpow_pos_of_pos hd _
  have hPowers : (1 + r) ^ (7 / 4 : ℝ) *
      (1 + r) ^ (-(19 / 8 : ℝ)) =
      (1 + r) ^ (-(5 / 8 : ℝ)) := by
    rw [← Real.rpow_add hd]
    norm_num
  apply (mul_le_mul_iff_left₀ hw).mp
  calc
    _ ≤ actualHartreePhysicalWeightedSourceConstant B A *
        ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) :=
      actual_Hartree_physical_full_interaction_weighted_pointwise
        ell c r B A hell hellOne hc hr hB hA z hz hSup hStrauss
    _ = (1 + r) ^ (7 / 4 : ℝ) *
        (actualHartreePhysicalWeightedSourceConstant B A *
          ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(19 / 8 : ℝ))) := by
      rw [← hPowers]
      ring

private theorem channel_pairing_le_physical_integrable_tail
    (ch : HartreeChannel) (G : ℝ → ℝ)
    (hG : InWeightedL2 (7 / 4 : ℝ) G) (M : ℝ)
    (hPoint : ∀ r : ℝ, 0 < r →
      |G r| ≤ M * (1 + r) ^ (-(19 / 8 : ℝ))) :
    |channelPairing ch G| ≤ M * actualHartreePhysicalChargeTailIntegral := by
  have hTail : IntegrableOn
      (fun r : ℝ => (1 + r) ^ (-(19 / 8 : ℝ))) (Ioi (0 : ℝ)) := by
    simpa only [add_comm] using
      (integrableOn_add_rpow_Ioi_of_lt
        (show -(19 / 8 : ℝ) < -1 by norm_num)
        (show -(1 : ℝ) < 0 by norm_num))
  have hMajor : IntegrableOn
      (fun r : ℝ => M * (1 + r) ^ (-(19 / 8 : ℝ))) (Ioi (0 : ℝ)) :=
    hTail.const_mul M
  have hPair : IntegrableOn
      (fun r : ℝ => channelResonance ch r * G r) (Ioi (0 : ℝ)) :=
    channel_data_pairing_integrableOn ch (7 / 4 : ℝ) (by norm_num) G hG
  have hBound (r : ℝ) (hr : 0 < r) :
      ‖channelResonance ch r * G r‖ ≤
        M * (1 + r) ^ (-(19 / 8 : ℝ)) := by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |channelResonance ch r| * |G r| ≤ |G r| := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (channelResonance_abs_le_one ch r hr.le) (abs_nonneg (G r))
      _ ≤ M * (1 + r) ^ (-(19 / 8 : ℝ)) := hPoint r hr
  calc
    |channelPairing ch G| =
        ‖∫ r in Ioi (0 : ℝ), channelResonance ch r * G r‖ := by
      rw [Real.norm_eq_abs, channelPairing]
    _ ≤ ∫ r in Ioi (0 : ℝ), ‖channelResonance ch r * G r‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ioi (0 : ℝ), M * (1 + r) ^ (-(19 / 8 : ℝ)) := by
      apply integral_mono_ae hPair.norm hMajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hBound r hr
    _ = M * actualHartreePhysicalChargeTailIntegral := by
      rw [integral_const_mul]
      rfl

/-- The uniquely forced H+/H- affine slopes have genuine O(ell^(1/8))
size. The plus factor two is the reciprocal of its actual resonance
limit -1/2; the minus limit is one. Neither slope is assumed small. -/
theorem actual_Hartree_physical_affine_charges_one_eighth_gain
    (B A ell c : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    |actualPlusCharge
      (fun r => (actualHartreePhysicalSliceInteraction ell c z r).re)| ≤
      2 * (actualHartreePhysicalWeightedSourceConstant B A *
        ell ^ (1 / 8 : ℝ) * actualHartreePhysicalChargeTailIntegral) ∧
    |actualMinusCharge
      (fun r => (actualHartreePhysicalSliceInteraction ell c z r).im)| ≤
      actualHartreePhysicalWeightedSourceConstant B A *
        ell ^ (1 / 8 : ℝ) * actualHartreePhysicalChargeTailIntegral := by
  let Fp : ℝ → ℝ :=
    fun r => (actualHartreePhysicalSliceInteraction ell c z r).re
  let Fm : ℝ → ℝ :=
    fun r => (actualHartreePhysicalSliceInteraction ell c z r).im
  let M : ℝ := actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)
  obtain ⟨hp, hm⟩ := actual_Hartree_physical_source_two_weighted_channels
    B A ell c hB hA hell hellOne hc z hz hSup hStrauss
  have hPoint (r : ℝ) (hr : 0 < r) :
      ‖actualHartreePhysicalSliceInteraction ell c z r‖ ≤
        M * (1 + r) ^ (-(19 / 8 : ℝ)) :=
    actual_Hartree_physical_source_unweighted_pointwise
      B A ell c r hB hA hell hellOne hc hr z hz hSup hStrauss
  have hpPoint (r : ℝ) (hr : 0 < r) :
      |Fp r| ≤ M * (1 + r) ^ (-(19 / 8 : ℝ)) :=
    (Complex.abs_re_le_norm _).trans (hPoint r hr)
  have hmPoint (r : ℝ) (hr : 0 < r) :
      |Fm r| ≤ M * (1 + r) ^ (-(19 / 8 : ℝ)) :=
    (Complex.abs_im_le_norm _).trans (hPoint r hr)
  have hPlus := channel_pairing_le_physical_integrable_tail
    HartreeChannel.plus Fp hp M hpPoint
  have hMinus := channel_pairing_le_physical_integrable_tail
    HartreeChannel.minus Fm hm M hmPoint
  have hPlusAbs : |actualPlusCharge Fp| =
      2 * |channelPairing HartreeChannel.plus Fp| := by
    calc
      _ = |channelPairing HartreeChannel.plus Fp| / (1 / 2 : ℝ) := by
        simp [actualPlusCharge, channelLimit, abs_div]
      _ = 2 * |channelPairing HartreeChannel.plus Fp| := by ring
  have hMinusAbs : |actualMinusCharge Fm| =
      |channelPairing HartreeChannel.minus Fm| := by
    simp [actualMinusCharge, channelLimit, abs_div]
  change |actualPlusCharge Fp| ≤ 2 * (M * actualHartreePhysicalChargeTailIntegral) ∧
    |actualMinusCharge Fm| ≤ M * actualHartreePhysicalChargeTailIntegral
  constructor
  · rw [hPlusAbs]
    exact mul_le_mul_of_nonneg_left hPlus (by norm_num)
  · rw [hMinusAbs]
    exact hMinus

end HBL.TypeIIDynamicSelection
