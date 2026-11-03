import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedLocalizedInner
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalAffineChargeGain
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalInteractionChargeGain
import Mathlib.Tactic

/-!
# HBL revised 2.13: forced affine charges of the correct conjugated inner PDE source

The original 3D radial correction is q=r*u.  Its inhomogeneous
interaction source is r*F, NOT F.  On the genuine smooth inner
partition with radius R=ell^(-1/16), this source has the already
strictly accepted O(ell^(1/16)) weighted estimate and a uniquely
normalized two-channel Fredholm solution.

This theorem proves that the TWO affine resonance charges of THAT
SAME conjugated/localized physical nonlocal Hartree source are also
O(ell^(1/16)).  No arbitrary homogeneous boundary coefficients,
assumed charge smallness, Type-II concentration law, Kummer or remote
compatibility are used.  The remaining full residual and physical
three-region C1 matching are separate obligations.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- Both real forced resonance slopes of the CORRECT radially conjugated,
localized original Hartree source inherit the positive spatial scale
order ell^(1/16).  The constants are actual physical Riesz bounds and
one fixed, already proved convergent radial integral. -/
theorem actual_Hartree_conjugated_inner_forced_charges_one_sixteenth
    (ell c B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let G := actualHartreeRadiallyConjugatedInnerSource
      (actualHartreeSlowInnerRadius ell) ell c z
    let Q := (2 * actualHartreePhysicalWeightedSourceConstant B A) *
      ell ^ (1 / 16 : ℝ) * actualHartreePhysicalChargeTailConstant
    |actualPlusCharge (fun r => (G r).re)| ≤ 2 * Q ∧
      |actualMinusCharge (fun r => (G r).im)| ≤ Q := by
  let R : ℝ := actualHartreeSlowInnerRadius ell
  let F : ℝ → ℂ := actualHartreePhysicalSliceInteraction ell c z
  let G : ℝ → ℂ := actualHartreeRadiallyConjugatedInnerSource R ell c z
  let K : ℝ := actualHartreePhysicalWeightedSourceConstant B A
  let M : ℝ := (2 * K) * ell ^ (1 / 16 : ℝ)
  let gp : ℝ → ℝ := fun r => (G r).re
  let gm : ℝ → ℝ := fun r => (G r).im
  have hR : 0 < R := by
    dsimp [R, actualHartreeSlowInnerRadius]
    exact Real.rpow_pos_of_pos hell _
  have hK : 0 ≤ K :=
    actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hPower : R * ell ^ (1 / 8 : ℝ) =
      ell ^ (1 / 16 : ℝ) := by
    dsimp [R, actualHartreeSlowInnerRadius]
    rw [← Real.rpow_add hell]
    norm_num
  have hNormG (r : ℝ) (hr : 0 < r) :
      ‖G r‖ ≤ M * (1 + r) ^ (-(19 / 8 : ℝ)) := by
    have hRaw : ‖F r‖ ≤
        K * ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(19 / 8 : ℝ)) :=
      actual_Hartree_physical_source_unweighted_pointwise
        B A ell c r hB hA hell hellOne hc hr z hz hSup hStrauss
    have hMult :
        |r * actualHartreeInnerSourceCutoff R r| ≤ 2 * R :=
      actual_Hartree_inner_radial_multiplier_bound R r hR hr
    calc
      ‖G r‖ =
          |r * actualHartreeInnerSourceCutoff R r| * ‖F r‖ := by
        dsimp only [G,actualHartreeRadiallyConjugatedInnerSource]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (2 * R) *
          (K * ell ^ (1 / 8 : ℝ) *
            (1 + r) ^ (-(19 / 8 : ℝ))) := by
        exact mul_le_mul hMult hRaw
          (norm_nonneg _) (by positivity)
      _ = (2 * K) * (R * ell ^ (1 / 8 : ℝ)) *
          (1 + r) ^ (-(19 / 8 : ℝ)) := by ring
      _ = M * (1 + r) ^ (-(19 / 8 : ℝ)) := by
        rw [hPower]
        rfl
  have hG := actual_Hartree_conjugated_slow_inner_one_sixteenth
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hChannels :=
    actual_Hartree_one_complex_weighted_source_two_channels
      (7 / 4 : ℝ) G hG.1 hG.2.1
  have hMajor : IntegrableOn
      (fun r : ℝ => M * (1 + r) ^ (-(19 / 8 : ℝ)))
      (Ioi (0 : ℝ)) :=
    actual_Hartree_physical_charge_tail_integrable.const_mul M
  have hPairing (ch : HartreeChannel) (g : ℝ → ℝ)
      (hg : InWeightedL2 (7 / 4 : ℝ) g)
      (hBound : ∀ r : ℝ, 0 < r → |g r| ≤ ‖G r‖) :
      |channelPairing ch g| ≤ M * actualHartreePhysicalChargeTailConstant := by
    have hPairInt := channel_data_pairing_integrableOn
      ch (7 / 4 : ℝ) (by norm_num) g hg
    change |∫ r in Ioi (0 : ℝ), channelResonance ch r * g r| ≤
      M * actualHartreePhysicalChargeTailConstant
    calc
      _ = ‖∫ r in Ioi (0 : ℝ), channelResonance ch r * g r‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ r in Ioi (0 : ℝ), ‖channelResonance ch r * g r‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ r in Ioi (0 : ℝ),
          M * (1 + r) ^ (-(19 / 8 : ℝ)) := by
        apply integral_mono_ae hPairInt.norm hMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        have hr0 : 0 < r := hr
        calc
          ‖channelResonance ch r * g r‖ =
              |channelResonance ch r| * |g r| := by
            rw [Real.norm_eq_abs, abs_mul]
          _ ≤ 1 * ‖G r‖ :=
            mul_le_mul (channelResonance_abs_le_one ch r hr0.le)
              (hBound r hr0) (abs_nonneg _) zero_le_one
          _ = ‖G r‖ := one_mul _
          _ ≤ M * (1 + r) ^ (-(19 / 8 : ℝ)) := hNormG r hr0
      _ = M * actualHartreePhysicalChargeTailConstant := by
        rw [integral_const_mul]
        rfl
  have hp := hPairing HartreeChannel.plus gp hChannels.1
    (fun r _ => Complex.abs_re_le_norm (G r))
  have hm := hPairing HartreeChannel.minus gm hChannels.2
    (fun r _ => Complex.abs_im_le_norm (G r))
  have hPlus : |actualPlusCharge gp| =
      2 * |channelPairing HartreeChannel.plus gp| := by
    norm_num [actualPlusCharge, channelLimit, abs_div, abs_neg,
      div_eq_mul_inv, mul_comm]
  have hMinus : |actualMinusCharge gm| =
      |channelPairing HartreeChannel.minus gm| := by
    simp only [actualMinusCharge, channelLimit, div_one, abs_neg]
  change |actualPlusCharge gp| ≤
      2 * (M * actualHartreePhysicalChargeTailConstant) ∧
    |actualMinusCharge gm| ≤
      M * actualHartreePhysicalChargeTailConstant
  constructor
  · rw [hPlus]
    exact mul_le_mul_of_nonneg_left hp (by norm_num)
  · rw [hMinus]
    exact hm

end HBL.TypeIIDynamicSelection
