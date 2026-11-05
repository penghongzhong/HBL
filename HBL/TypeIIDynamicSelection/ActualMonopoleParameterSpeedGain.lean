import HBL.TypeIIDynamicSelection.MonopoleSourceTerminal
import HBL.MonopoleComplexResidual
import Mathlib.Tactic

/-!
# Actual source-driven Kummer parameter speed gain

The modulation coordinates are driven by the fixed normalized threshold
projections of the actual Hartree monopole residual.  The compact tests live
inside the normalized core, where the existing physical residual estimate is
uniform.  Hence the two coordinate speeds have a genuine positive time order.

No arbitrary mu_s or theta_s is introduced.  This file does not estimate the
independent time derivative of a general annular Hartree source.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation
open HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

def actualMonopoleThresholdTestMass : ℝ :=
  ∫ r in Ioi (0 : ℝ),
    (|r * normalizedZetaPlus r| + |r * normalizedZetaMinus r|)

private theorem threshold_plus_abs_weight_integrable :
    Integrable (fun r : ℝ => |r * normalizedZetaPlus r|) := by
  have hc : Continuous (fun r : ℝ => r * normalizedZetaPlus r) :=
    continuous_id.mul normalizedZetaPlus_contDiff_infty.continuous
  have hs : HasCompactSupport (fun r : ℝ => r * normalizedZetaPlus r) :=
    normalizedZetaPlus_hasCompactSupport.mul_left
  have hi := hc.integrable_of_hasCompactSupport (μ := volume) hs
  simpa only [Real.norm_eq_abs] using hi.norm

private theorem threshold_minus_abs_weight_integrable :
    Integrable (fun r : ℝ => |r * normalizedZetaMinus r|) := by
  have hc : Continuous (fun r : ℝ => r * normalizedZetaMinus r) :=
    continuous_id.mul normalizedZetaMinus_contDiff_infty.continuous
  have hs : HasCompactSupport (fun r : ℝ => r * normalizedZetaMinus r) :=
    normalizedZetaMinus_hasCompactSupport.mul_left
  have hi := hc.integrable_of_hasCompactSupport (μ := volume) hs
  simpa only [Real.norm_eq_abs] using hi.norm

theorem actualMonopoleThresholdTestMass_nonneg :
    0 ≤ actualMonopoleThresholdTestMass := by
  unfold actualMonopoleThresholdTestMass
  exact integral_nonneg fun r => add_nonneg (abs_nonneg _) (abs_nonneg _)

def actualMonopoleParameterGain (beta : ℝ) : ℝ :=
  min (2 * beta - 1) beta

theorem actual_monopole_parameter_gain_positive
    (beta : ℝ) (hbeta : 1 / 2 < beta) :
    0 < actualMonopoleParameterGain beta := by
  unfold actualMonopoleParameterGain
  exact lt_min (by linarith) (by linarith)

/-- The two ACTUAL fixed threshold-coordinate speeds inherit a strict
s^(-1-delta) bound from the already proved core Hartree residual, where
delta=min(2 beta-1,beta)>0.  The constant is independent of the path,
s, beta and A. -/
theorem actual_monopole_threshold_coordinate_speed_gain :
    ∃ C : ℝ, 0 < C ∧
      ∀ {c b omega : ℝ → ℝ} {s0 beta A : ℝ},
      1 ≤ s0 → 1 / 2 < beta → 0 ≤ A →
      Differentiable ℝ c → Measurable b → Measurable omega →
      (∀ s : ℝ, s0 < s → |c s| ≤ 1) →
      (∀ s : ℝ, s0 < s →
        |c s| ≤ A * s ^ (-beta) ∧
        |deriv c s| ≤ A * s ^ (-1 - beta) ∧
        |b s| ≤ A * s ^ (-1 : ℝ) ∧
        |omega s| ≤ A * s ^ (-1 : ℝ)) →
      ∀ s : ℝ, s0 < s →
      |monopoleThresholdCoordinatePlus c b omega s| +
        |monopoleThresholdCoordinateMinus c b omega s| ≤
      C * (A + A ^ 2) *
        s ^ (-1 - actualMonopoleParameterGain beta) := by
  obtain ⟨D, hD, hResidual⟩ := monopoleComplexEffectiveIncrement_core_bound
  let Mtest := actualMonopoleThresholdTestMass
  let C0 := monopoleStaticRadialBoundConstant +
    2 * monopoleRadialBoundConstant + D
  let C := 1 + Mtest * C0
  have hMass : 0 ≤ Mtest := by
    dsimp [Mtest]
    exact actualMonopoleThresholdTestMass_nonneg
  have hStatic : 0 < monopoleStaticRadialBoundConstant :=
    monopoleStaticRadialBoundConstant_pos
  have hRad : 0 < monopoleRadialBoundConstant :=
    monopoleRadialBoundConstant_pos
  have hC0 : 0 < C0 := by
    dsimp [C0]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro c b omega s0 beta A hs0 hbeta hA hc hb homega hsmall hdecay s hs
  have hRows := (monopoleThresholdCoordinates_integrable
    (s0 := s0) (beta := beta) (A := A)
    (by linarith : 0 < s0) hbeta hA hc hb homega hsmall hdecay).1 s hs
  let K : ℝ :=
    monopoleStaticRadialBoundConstant * (c s) ^ 2 +
      monopoleRadialBoundConstant * |deriv c s| +
      D * |b s * c s| +
      monopoleRadialBoundConstant * |omega s * c s|
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hPoint (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
      ‖monopoleComplexEffectiveIncrement c (b s) (omega s) s r‖ ≤ K := by
    have hcr : |c s| * r ≤ 1 := by
      simpa only [one_mul] using
        (mul_le_mul (hsmall s hs) hr1 hr.le (by norm_num : (0 : ℝ) ≤ 1))
    have h :=
      hResidual c (deriv c s) s r (b s) (omega s)
        (hc s).hasDerivAt (hsmall s hs) hr (by nlinarith [hcr])
    simpa only [K] using h
  have hPlus : |monopoleThresholdCoordinatePlus c b omega s| ≤
      K * ∫ r in Ioi (0 : ℝ), |r * normalizedZetaPlus r| := by
    rw [monopoleThresholdCoordinatePlus_eq_halfLine]
    calc
      _ ≤ ∫ r in Ioi (0 : ℝ),
          |normalizedZetaPlus r *
            radialU (fun x =>
              (monopoleComplexEffectiveIncrement c (b s) (omega s) s x).re) r| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ r in Ioi (0 : ℝ), K * |r * normalizedZetaPlus r| := by
        apply integral_mono_ae hRows.1.abs
          (threshold_plus_abs_weight_integrable.const_mul K).integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        by_cases hr1 : r ≤ 1
        · have hv := (Complex.abs_re_le_norm
            (monopoleComplexEffectiveIncrement c (b s) (omega s) s r)).trans
              (hPoint r hr hr1)
          simp only [radialU, abs_mul]
          calc
            |normalizedZetaPlus r| *
                (|r| * |(monopoleComplexEffectiveIncrement
                  c (b s) (omega s) s r).re|) =
              (|r| * |normalizedZetaPlus r|) *
                |(monopoleComplexEffectiveIncrement
                  c (b s) (omega s) s r).re| := by ring
            _ ≤ (|r| * |normalizedZetaPlus r|) * K :=
              mul_le_mul_of_nonneg_left hv (by positivity)
            _ = K * (|r| * |normalizedZetaPlus r|) := by ring
        · have hr1' : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
          rw [normalizedZetaPlus_zero_of_one_le r hr1']
          simp
      _ = _ := by rw [integral_const_mul]
  have hMinus : |monopoleThresholdCoordinateMinus c b omega s| ≤
      K * ∫ r in Ioi (0 : ℝ), |r * normalizedZetaMinus r| := by
    rw [monopoleThresholdCoordinateMinus_eq_halfLine]
    calc
      _ ≤ ∫ r in Ioi (0 : ℝ),
          |normalizedZetaMinus r *
            radialU (fun x =>
              (monopoleComplexEffectiveIncrement c (b s) (omega s) s x).im) r| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ r in Ioi (0 : ℝ), K * |r * normalizedZetaMinus r| := by
        apply integral_mono_ae hRows.2.abs
          (threshold_minus_abs_weight_integrable.const_mul K).integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        by_cases hr1 : r ≤ 1
        · have hv := (Complex.abs_im_le_norm
            (monopoleComplexEffectiveIncrement c (b s) (omega s) s r)).trans
              (hPoint r hr hr1)
          simp only [radialU, abs_mul]
          calc
            |normalizedZetaMinus r| *
                (|r| * |(monopoleComplexEffectiveIncrement
                  c (b s) (omega s) s r).im|) =
              (|r| * |normalizedZetaMinus r|) *
                |(monopoleComplexEffectiveIncrement
                  c (b s) (omega s) s r).im| := by ring
            _ ≤ (|r| * |normalizedZetaMinus r|) * K :=
              mul_le_mul_of_nonneg_left hv (by positivity)
            _ = K * (|r| * |normalizedZetaMinus r|) := by ring
        · have hr1' : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
          rw [normalizedZetaMinus_zero_of_one_le r hr1']
          simp
      _ = _ := by rw [integral_const_mul]
  have hIp := threshold_plus_abs_weight_integrable.integrableOn
  have hIm := threshold_minus_abs_weight_integrable.integrableOn
  have hMassEq :
      (∫ r in Ioi (0 : ℝ), |r * normalizedZetaPlus r|) +
        (∫ r in Ioi (0 : ℝ), |r * normalizedZetaMinus r|) = Mtest := by
    dsimp [Mtest, actualMonopoleThresholdTestMass]
    rw [integral_add hIp hIm]
  have hCoord : |monopoleThresholdCoordinatePlus c b omega s| +
      |monopoleThresholdCoordinateMinus c b omega s| ≤ Mtest * K := by
    calc
      _ ≤ K * (∫ r in Ioi (0 : ℝ), |r * normalizedZetaPlus r|) +
          K * (∫ r in Ioi (0 : ℝ), |r * normalizedZetaMinus r|) :=
        add_le_add hPlus hMinus
      _ = K * Mtest := by rw [← hMassEq]; ring
      _ = Mtest * K := by ring
  obtain ⟨hcs, hcd, hbs, hos⟩ := hdecay s hs
  have hs1 : 1 ≤ s := hs0.trans hs.le
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hd1 : actualMonopoleParameterGain beta ≤ 2 * beta - 1 := min_le_left _ _
  have hd2 : actualMonopoleParameterGain beta ≤ beta := min_le_right _ _
  have hp2 :
      s ^ (-2 * beta) ≤ s ^ (-1 - actualMonopoleParameterGain beta) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hp1 :
      s ^ (-1 - beta) ≤ s ^ (-1 - actualMonopoleParameterGain beta) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hc2 : (c s) ^ 2 ≤ A ^ 2 * s ^ (-2 * beta) := by
    calc
      (c s) ^ 2 = |c s| ^ 2 := (sq_abs (c s)).symm
      _ ≤ (A * s ^ (-beta)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = A ^ 2 * (s ^ (-beta)) ^ 2 := by ring
      _ = A ^ 2 * s ^ (-2 * beta) := by
        rw [← Real.rpow_mul_natCast hspos.le (-beta) 2]
        congr 2
        ring
  have hbc : |b s * c s| ≤ A ^ 2 * s ^ (-1 - beta) := by
    rw [abs_mul]
    calc
      |b s| * |c s| ≤
          (A * s ^ (-1 : ℝ)) * (A * s ^ (-beta)) :=
        mul_le_mul hbs hcs (abs_nonneg _) (by positivity)
      _ = A ^ 2 * (s ^ (-1 : ℝ) * s ^ (-beta)) := by ring
      _ = A ^ 2 * s ^ (-1 - beta) := by
        rw [← Real.rpow_add hspos]
        congr 2
        ring
  have hoc : |omega s * c s| ≤ A ^ 2 * s ^ (-1 - beta) := by
    rw [abs_mul]
    calc
      |omega s| * |c s| ≤
          (A * s ^ (-1 : ℝ)) * (A * s ^ (-beta)) :=
        mul_le_mul hos hcs (abs_nonneg _) (by positivity)
      _ = A ^ 2 * (s ^ (-1 : ℝ) * s ^ (-beta)) := by ring
      _ = A ^ 2 * s ^ (-1 - beta) := by
        rw [← Real.rpow_add hspos]
        congr 2
        ring
  let W := (A + A ^ 2) *
    s ^ (-1 - actualMonopoleParameterGain beta)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hStaticTerm :
      monopoleStaticRadialBoundConstant * (c s) ^ 2 ≤
        monopoleStaticRadialBoundConstant * W := by
    dsimp [W]
    gcongr
    calc
      (c s)^2 ≤ A^2 * s^(-2*beta) := hc2
      _ ≤ A^2 * s^(-1-actualMonopoleParameterGain beta) :=
        mul_le_mul_of_nonneg_left hp2 (sq_nonneg A)
      _ ≤ (A+A^2) * s^(-1-actualMonopoleParameterGain beta) := by
        gcongr
        linarith
  have hDerivTerm :
      monopoleRadialBoundConstant * |deriv c s| ≤
        monopoleRadialBoundConstant * W := by
    dsimp [W]
    gcongr
    calc
      |deriv c s| ≤ A * s^(-1-beta) := hcd
      _ ≤ A * s^(-1-actualMonopoleParameterGain beta) :=
        mul_le_mul_of_nonneg_left hp1 hA
      _ ≤ (A+A^2) * s^(-1-actualMonopoleParameterGain beta) := by
        gcongr
        nlinarith [sq_nonneg A]
  have hBTerm : D * |b s * c s| ≤ D * W := by
    dsimp [W]
    gcongr
    calc
      |b s*c s| ≤ A^2 * s^(-1-beta) := hbc
      _ ≤ A^2 * s^(-1-actualMonopoleParameterGain beta) :=
        mul_le_mul_of_nonneg_left hp1 (sq_nonneg A)
      _ ≤ (A+A^2) * s^(-1-actualMonopoleParameterGain beta) := by
        gcongr
        linarith
  have hOmegaTerm :
      monopoleRadialBoundConstant * |omega s * c s| ≤
        monopoleRadialBoundConstant * W := by
    dsimp [W]
    gcongr
    calc
      |omega s*c s| ≤ A^2 * s^(-1-beta) := hoc
      _ ≤ A^2 * s^(-1-actualMonopoleParameterGain beta) :=
        mul_le_mul_of_nonneg_left hp1 (sq_nonneg A)
      _ ≤ (A+A^2) * s^(-1-actualMonopoleParameterGain beta) := by
        gcongr
        linarith
  have hRaw : K ≤ C0 * W := by
    dsimp [K, C0]
    nlinarith only [hStaticTerm, hDerivTerm, hBTerm, hOmegaTerm]
  calc
    _ ≤ Mtest * K := hCoord
    _ ≤ Mtest * (C0 * W) := mul_le_mul_of_nonneg_left hRaw hMass
    _ ≤ C * W := by
      dsimp [C]
      have hMC : 0 ≤ Mtest * C0 := mul_nonneg hMass hC0.le
      nlinarith
    _ = C * (A + A ^ 2) *
        s ^ (-1 - actualMonopoleParameterGain beta) := by
      dsimp [W]
      ring

end HBL.TypeIIDynamicSelection
