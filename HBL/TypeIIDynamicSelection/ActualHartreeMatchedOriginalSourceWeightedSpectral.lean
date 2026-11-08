import HBL.TypeIIDynamicSelection.ActualHartreeMatchedKummerInteriorSourceBound
import HBL.TypeIIDynamicSelection.ActualHartreeOriginalSpectralC1TraceNoRadiusLoss
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralRegularizedQuadratic
import Mathlib.Tactic

/-!
# Matched spectral quadratic gain with no independent profile upper bound

For the genuine Cramer/Fredholm-compatible left value and slope, the
singular homogeneous coefficient is exactly zero. The original
inverse-square source controls the true Green value with no explicit
inverse left matching radius; the remaining regular coefficient is
determined by the same left Cauchy coordinates.

This PRODUCES the weighted first matched profile and feeds it into the
original zero-left-jet Volterra spectral correction. No arbitrary
weighted bound on that profile is assumed in the final theorem below.
The left Cauchy jet must still come from the same physical inner Fredholm
trajectory to complete §2.13. The Kummer basis norm C may still depend
on the moving left radius; no time decay or Type-II rate is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The genuine left-compatible matched first field has an r-weighted
bound DERIVED from its actual source and its original Fredholm left jet. -/
theorem actual_Hartree_matched_original_source_weighted_first_profile
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C Q : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ Q / x ^ 2)
    (U DU : ℂ)
    (hCompatible : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖(r : ℂ) * actualOriginMatchedKummerValue K a b F U DU r‖ ≤
      b * ((2 * C ^ 2 * (b - a)) * Q +
        C ^ 3 * (‖U‖ + ‖DU‖)) := by
  have hZeroSing : actualOriginMatchedSingularCoeff K a b F U DU = 0 :=
    (actual_origin_matched_Kummer_singular_eq_obstruction K hK hab F U DU).trans
      hCompatible
  have hGreen :=
    originGreen_inverse_square_value_slope_no_left_radius_loss
      K a b C Q ha hC hQ hK F hF hr
  have hGreenValue :
      ‖originGreenValue K a b F r‖ ≤ (2 * C ^ 2 * (b - a)) * Q := by
    have hslope : 0 ≤ ‖originGreenSlope K a b F r‖ := norm_nonneg _
    linarith only [hGreen, hslope]
  have hCoeff :=
    actual_Hartree_matched_Kummer_regular_coefficient_from_left_jet
      K a b C hC hK hab F U DU
  rcases hK r hr with ⟨_, _, _, _, _, _, _, _, hx, _, _⟩
  have hCjet : 0 ≤ C ^ 2 * (‖U‖ + ‖DU‖) := by positivity
  have hMultiply :
      ‖actualOriginMatchedRegularCoeff K a b F U DU‖ *
        ‖originPhysicalValue K.x r‖ ≤
          (C ^ 2 * (‖U‖ + ‖DU‖)) * C :=
    mul_le_mul hCoeff hx (norm_nonneg _) hCjet
  have hWhole :
      ‖actualOriginMatchedKummerValue K a b F U DU r‖ ≤
        (2 * C ^ 2 * (b - a)) * Q + C ^ 3 * (‖U‖ + ‖DU‖) := by
    calc
      _ = ‖originGreenValue K a b F r +
          actualOriginMatchedRegularCoeff K a b F U DU *
            originPhysicalValue K.x r‖ := by
        simp [actualOriginMatchedKummerValue, hZeroSing]
      _ ≤ ‖originGreenValue K a b F r‖ +
          ‖actualOriginMatchedRegularCoeff K a b F U DU *
            originPhysicalValue K.x r‖ := norm_add_le _ _
      _ = ‖originGreenValue K a b F r‖ +
          ‖actualOriginMatchedRegularCoeff K a b F U DU‖ *
            ‖originPhysicalValue K.x r‖ := by rw [norm_mul]
      _ ≤ (2 * C ^ 2 * (b - a)) * Q +
          (C ^ 2 * (‖U‖ + ‖DU‖)) * C :=
        add_le_add hGreenValue hMultiply
      _ = (2 * C ^ 2 * (b - a)) * Q +
          C ^ 3 * (‖U‖ + ‖DU‖) := by ring
  have hrpos : 0 < r := ha.trans_le hr.1
  have hnormr : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  have hb0 : 0 ≤ b := ha.le.trans hab
  calc
    ‖(r : ℂ) * actualOriginMatchedKummerValue K a b F U DU r‖ =
        r * ‖actualOriginMatchedKummerValue K a b F U DU r‖ := by
          rw [norm_mul, hnormr]
    _ ≤ b * ((2 * C ^ 2 * (b - a)) * Q +
        C ^ 3 * (‖U‖ + ‖DU‖)) :=
      mul_le_mul hr.2 hWhole (norm_nonneg _) hb0

/-- A genuine source-to-first-matched-profile-to-second-Green estimate.
The weighted first-profile hypothesis is CONSTRUCTED above, not passed
as an independent premise to this theorem. -/
theorem actual_Hartree_matched_original_source_quadratic_spectral_error
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G Q : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hQ : 0 ≤ Q)
    (hK : OriginBasisOn K a b C)
    (hbound : ∀ x ∈ Icc 0 scale,
        ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ) (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ Q / x ^ 2)
    (U DU d : ℂ)
    (hCompatible : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖d * actualOriginMatchedKummerValue K a b
      (actualHartreeMatchedSpectralFirstSource K a b F U DU d) 0 0 r‖ ≤
      (2 * G ^ 2 * (b - a)) *
        (‖d‖ ^ 2 *
          (b * ((2 * C ^ 2 * (b - a)) * Q +
            C ^ 3 * (‖U‖ + ‖DU‖)))) / r := by
  let H : ℝ :=
    b * ((2 * C ^ 2 * (b - a)) * Q +
      C ^ 3 * (‖U‖ + ‖DU‖))
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hb0 : 0 ≤ b := ha.le.trans hab
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hProfile : ∀ x ∈ Icc a b,
      ‖(x : ℂ) * actualOriginMatchedKummerValue K a b F U DU x‖ ≤ H := by
    intro x hx
    exact actual_Hartree_matched_original_source_weighted_first_profile
      K a b C Q ha hab hC hQ hK F hF U DU hCompatible x hx
  exact actual_Hartree_matched_spectral_quadratic_defect_weighted
    K a b C G H ha hab hb hG hH hK hbound F U DU d hProfile r hr

end HBL.TypeIIDynamicSelection
