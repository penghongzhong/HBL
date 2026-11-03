import HBL.TypeIIDynamicSelection.ActualHartreePhysicalInteractionInnerSolve
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The two forced physical affine charges retain the Hartree source gain

Existence of the inner Fredholm correction alone does not control the
boundary coefficients. Here both charges of the same actual complete
Hartree interaction are quantitatively O(ell^(1/8)). The constant is an
explicit convergent half-line integral times the previously derived
physical source constant. No free boundary coefficient, weighted-source
estimate, matching compatibility, or time-concentration law is assumed.

This does not yet bound all classical inner traces or match the remote
Kummer endpoint. It is a quantitative input to that remaining problem.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- The unweighted physical source envelope has an integrable tail.
This explicit integrability prevents use of an undefined Bochner integral. -/
theorem actual_Hartree_physical_charge_tail_integrable :
    IntegrableOn (fun r : ℝ => (1 + r) ^ (-(19 / 8 : ℝ)))
      (Ioi (0 : ℝ)) := by
  simpa only [add_comm] using
    (integrableOn_add_rpow_Ioi_of_lt
      (a := -(19 / 8 : ℝ)) (c := 0) (m := 1)
      (by norm_num) (by norm_num))

def actualHartreePhysicalChargeTailConstant : ℝ :=
  ∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(19 / 8 : ℝ))

/-- The same original nonlocal interaction forces small, rather than
arbitrary, inner affine slopes in both physical Hartree channels. -/
theorem actual_Hartree_physical_interaction_forced_charges_one_eighth
    (ell c B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let F : ℝ → ℂ := actualHartreePhysicalSliceInteraction ell c z
    let Q : ℝ := actualHartreePhysicalWeightedSourceConstant B A *
      ell ^ (1 / 8 : ℝ) * actualHartreePhysicalChargeTailConstant
    |actualPlusCharge (fun r => (F r).re)| ≤ 2 * Q ∧
      |actualMinusCharge (fun r => (F r).im)| ≤ Q := by
  let F : ℝ → ℂ := actualHartreePhysicalSliceInteraction ell c z
  let M : ℝ := actualHartreePhysicalWeightedSourceConstant B A *
    ell ^ (1 / 8 : ℝ)
  have hNormF (r : ℝ) (hr : 0 < r) :
      ‖F r‖ ≤ M * (1 + r) ^ (-(19 / 8 : ℝ)) := by
    have hd : 0 < 1 + r := by linarith
    have hWeight : 0 < (1 + r) ^ (7 / 4 : ℝ) :=
      Real.rpow_pos_of_pos hd _
    apply (mul_le_mul_left hWeight).mp
    calc
      (1 + r) ^ (7 / 4 : ℝ) * ‖F r‖ ≤
          M * (1 + r) ^ (-(5 / 8 : ℝ)) := by
        exact actual_Hartree_physical_full_interaction_weighted_pointwise
          ell c r B A hell hellOne hc hr hB hA z hz hSup hStrauss
      _ = (1 + r) ^ (7 / 4 : ℝ) *
          (M * (1 + r) ^ (-(19 / 8 : ℝ))) := by
        have he : (1 + r) ^ (7 / 4 : ℝ) *
            (1 + r) ^ (-(19 / 8 : ℝ)) =
            (1 + r) ^ (-(5 / 8 : ℝ)) := by
          rw [← Real.rpow_add hd]
          norm_num
        calc
          _ = M * ((1 + r) ^ (7 / 4 : ℝ) *
              (1 + r) ^ (-(19 / 8 : ℝ))) := by rw [he]
          _ = _ := by ring
  have hMajor : IntegrableOn
      (fun r : ℝ => M * (1 + r) ^ (-(19 / 8 : ℝ)))
      (Ioi (0 : ℝ)) :=
    actual_Hartree_physical_charge_tail_integrable.const_mul M
  have hPairBound (ch : HartreeChannel) (g : ℝ → ℝ)
      (hg : InWeightedL2 (7 / 4 : ℝ) g)
      (hDom : ∀ r : ℝ, 0 < r → |g r| ≤ ‖F r‖) :
      |channelPairing ch g| ≤ M * actualHartreePhysicalChargeTailConstant := by
    have hInt := channel_data_pairing_integrableOn
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
        apply integral_mono_ae hInt.norm hMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        have hr0 : 0 < r := hr
        calc
          ‖channelResonance ch r * g r‖ =
              |channelResonance ch r| * |g r| := by
            rw [Real.norm_eq_abs, abs_mul]
          _ ≤ 1 * ‖F r‖ :=
            mul_le_mul (channelResonance_abs_le_one ch r hr0.le)
              (hDom r hr0) (abs_nonneg _) zero_le_one
          _ = ‖F r‖ := one_mul _
          _ ≤ M * (1 + r) ^ (-(19 / 8 : ℝ)) := hNormF r hr0
      _ = M * actualHartreePhysicalChargeTailConstant := by
        rw [integral_const_mul]
  have hChannels := actual_Hartree_physical_interaction_inner_channels
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hp := hPairBound HartreeChannel.plus (fun r => (F r).re)
    hChannels.1 (fun r _ => Complex.abs_re_le_norm (F r))
  have hm := hPairBound HartreeChannel.minus (fun r => (F r).im)
    hChannels.2 (fun r _ => Complex.abs_im_le_norm (F r))
  have hPlus : |actualPlusCharge (fun r => (F r).re)| =
      2 * |channelPairing HartreeChannel.plus (fun r => (F r).re)| := by
    norm_num [actualPlusCharge, channelLimit, abs_div, abs_neg,
      div_eq_mul_inv, mul_comm]
  have hMinus : |actualMinusCharge (fun r => (F r).im)| =
      |channelPairing HartreeChannel.minus (fun r => (F r).im)| := by
    simp only [actualMinusCharge, channelLimit, div_one, abs_neg]
  constructor
  · rw [hPlus]
    exact mul_le_mul_of_nonneg_left hp (by norm_num)
  · rw [hMinus]
    exact hm

end HBL.TypeIIDynamicSelection
