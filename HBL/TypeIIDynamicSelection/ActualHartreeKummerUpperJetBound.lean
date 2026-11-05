import HBL.TypeIIDynamicSelection.ActualHartreeMatchedExteriorGrowth
import HBL.TypeIIDynamicSelection.ActualHartreeKummerRegularTailGain
import Mathlib.Tactic

/-!
# Compatibility-cancelled Kummer upper jet

After the full coupled compatibility condition is zero, the singular
origin mode vanishes exactly. The whole upper Cauchy jet is therefore one
regular basis jet times a single forced scalar coefficient. This file
quantifies that scalar from the actual left Cauchy jet and the regular
Green source coefficient.

No remote boundary condition, abstract source order, or small upper jet is
assumed. The theorem is deliberately generic so that subsequent residual
layers can reuse it with their own actual source bounds.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Zero compatibility eliminates the singular Kummer mode. The remaining
upper value/slope are controlled with no moving-left-endpoint amplification. -/
theorem actual_matched_Kummer_upper_regular_jet_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B r0 J T : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hr0 : 0 < r0) (hOrder : r0 ≤ B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (F : ℝ → ℂ) (U DU : ℂ)
    (hzero : actualMomentLockedIntervalObstruction K r0 B F U DU = 0)
    (hJ : ‖U‖ + r0 * ‖DU‖ ≤ J) (hJ0 : 0 ≤ J)
    (hT : ‖originGreenCoeffB K r0 F B‖ ≤ T) (hT0 : 0 ≤ T) :
    let C0 := 1 + (D + 1) * G * B ^ 2
    let H := (D + 1) * G
    ‖actualOriginMatchedKummerValue K r0 B F U DU B‖ +
      B * ‖actualOriginMatchedKummerSlope K r0 B F U DU B‖ ≤
      (C0 + 2 * H * B ^ 2) * (2 * G * J + T) := by
  dsimp only
  let C0 := 1 + (D + 1) * G * B ^ 2
  let H := (D + 1) * G
  have hB : 0 < B := hr0.trans_le hOrder
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hK : OriginBasisOn K r0 B G :=
    origin_kummer_annulus_bound K r0 B G hr0 hBR hG hbound
  have hBeta0 :=
    actual_matched_Kummer_regular_coefficient_bound
      K G B r0 hG hr0 hOrder hBOne hBR hbound F U DU
  have hJetTerms : 0 ≤ ‖U‖ + r0 * ‖DU‖ := by positivity
  have hBeta :
      ‖actualOriginMatchedRegularCoeff K r0 B F U DU‖ ≤ 2 * G * J := by
    calc
      _ ≤ G * (r0 * ‖DU‖) + 2 * G * ‖U‖ := hBeta0
      _ ≤ 2 * G * (‖U‖ + r0 * ‖DU‖) := by
        nlinarith [mul_nonneg hG (mul_nonneg hr0.le (norm_nonneg DU)),
          mul_nonneg hG (norm_nonneg U)]
      _ ≤ 2 * G * J :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
  let gamma : ℂ :=
    actualOriginMatchedRegularCoeff K r0 B F U DU +
      originGreenCoeffB K r0 F B
  have hGamma : ‖gamma‖ ≤ 2 * G * J + T := by
    dsimp [gamma]
    exact (norm_add_le _ _).trans (add_le_add hBeta hT)
  have hGamma0 : 0 ≤ 2 * G * J + T := by
    positivity
  have hReg :=
    origin_kummer_regular_physical_bound
      K D G hD hG hBR.le hcoeff hbound B ⟨hB, hBR.le⟩
  have hExact :=
    actual_origin_matched_Kummer_upper_regular_jet
      K hK hOrder F U DU hzero
  have hValue :
      ‖actualOriginMatchedKummerValue K r0 B F U DU B‖ ≤ C0 * ‖gamma‖ := by
    rw [hExact.1, norm_mul]
    exact mul_le_mul_of_nonneg_right hReg.1 (norm_nonneg _)
  have hSlope :
      ‖actualOriginMatchedKummerSlope K r0 B F U DU B‖ ≤
        (2 * H * B) * ‖gamma‖ := by
    rw [hExact.2, norm_mul]
    exact mul_le_mul_of_nonneg_right hReg.2 (norm_nonneg _)
  have hFactor : 0 ≤ C0 + 2 * H * B ^ 2 := by positivity
  calc
    ‖actualOriginMatchedKummerValue K r0 B F U DU B‖ +
        B * ‖actualOriginMatchedKummerSlope K r0 B F U DU B‖ ≤
      C0 * ‖gamma‖ + B * ((2 * H * B) * ‖gamma‖) :=
        add_le_add hValue (mul_le_mul_of_nonneg_left hSlope hB.le)
    _ = (C0 + 2 * H * B ^ 2) * ‖gamma‖ := by ring
    _ ≤ (C0 + 2 * H * B ^ 2) * (2 * G * J + T) :=
      mul_le_mul_of_nonneg_left hGamma hFactor

end HBL.TypeIIDynamicSelection
