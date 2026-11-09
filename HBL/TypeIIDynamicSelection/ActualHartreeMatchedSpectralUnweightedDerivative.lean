import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftVolterraUnweightedSlope
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralRegularizedQuadratic
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummerClassical
import Mathlib.Tactic

/-!
# Genuine matched Hartree spectral Green: unweighted radial derivative

The literal first spectral forcing is q=d*w₀ for the original complete
Cramer-matched Kummer profile w₀. Its inverse-linear source bound follows
from the radius-weighted original profile, rather than an independent bound
on q. The original regularized Wronskian moment estimate then controls
the ACTUAL unweighted derivative of the zero-left Green correction with
no inverse moving-left-radius factor.

This is stronger than the radius-squared weighted C¹ estimate, but
remains a static fixed-Kummer-interval result. It does not impose a
physical clock, positive time residual, bubble envelope for all four
moving regions, or Type-II blowup rate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The first original matched spectral correction has an unweighted
ACTUAL spatial derivative bound uniform as the left endpoint tends to
zero. The first source q=d*w₀ comes from the same original matched
profile; no separately postulated q-envelope or new speed is used. -/
theorem actual_Hartree_original_matched_spectral_unweighted_C1_no_left_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b D G H : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Ioo 0 scale, ContinuousAt F x)
    (U DU d : ℂ)
    (hProfile : ∀ x ∈ Icc a b,
      ‖(x : ℂ) * actualOriginMatchedKummerValue K a b F U DU x‖ ≤ H)
    (r : ℝ) (hr : r ∈ Icc a b) :
    let q := actualHartreeMatchedSpectralFirstSource K a b F U DU d
    let w₁ := actualOriginMatchedKummerValue K a b q 0 0
    ‖deriv w₁ r‖ ≤
      (b + 1) * G * (1 + (D + 1) * G * b ^ 2) * (‖d‖ * H) +
      2 * (D + 1) * G ^ 2 * (‖d‖ * H) * b ^ 2 := by
  dsimp only
  let C : ℝ := G * (1 / a + 1 / a ^ 2) + b ^ 2 + 1
  let M : ℝ := ‖d‖ * H
  let u : ℝ → ℂ := actualOriginMatchedKummerValue K a b F U DU
  let q : ℝ → ℂ := actualHartreeMatchedSpectralFirstSource K a b F U DU d
  let w₁ : ℝ → ℂ := actualOriginMatchedKummerValue K a b q 0 0
  have hM : 0 ≤ M := mul_nonneg (norm_nonneg d) hH
  have hK : OriginBasisOn K a b C :=
    origin_kummer_annulus_bound K a b G ha hb hG hbound
  have hQ : ∀ x ∈ Icc a b, ‖q x‖ ≤ M / x := by
    intro x hx
    exact actual_Hartree_matched_spectral_first_source_inverse_linear
      K a b H ha hH F U DU d hProfile x hx
  have hU :=
    actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb F hF U DU
  have hQcont : ∀ x ∈ Ioo (0 : ℝ) scale, ContinuousAt q x := by
    intro x hx
    change ContinuousAt (fun y : ℝ => d * u y) x
    exact continuousAt_const.mul ((hU x hx).1.continuousAt)
  have hrPos : r ∈ Ioo (0 : ℝ) scale :=
    ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  have hActualDerivative :
      deriv w₁ r = actualOriginMatchedKummerSlope K a b q 0 0 r :=
    (actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb q hQcont 0 0 r hrPos).1.deriv
  have hSlope :=
    actual_Hartree_zero_left_Kummer_Volterra_unweighted_slope_no_left_radius
      K a b C D G M ha hab hb hD hG hM hK hcoeff hbound
      q hQcont hQ r hr
  change ‖deriv w₁ r‖ ≤ _
  rw [hActualDerivative]
  simpa only [M, q] using hSlope

/-- The same unweighted derivative estimate is literally the difference
between the frozen original matched slope and the spectrally corrected
matched slope; it is not an abstract C¹ source assumption. -/
theorem actual_Hartree_original_spectral_corrected_derivative_gap_no_left_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b D G H : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Ioo 0 scale, ContinuousAt F x)
    (U DU d : ℂ)
    (hProfile : ∀ x ∈ Icc a b,
      ‖(x : ℂ) * actualOriginMatchedKummerValue K a b F U DU x‖ ≤ H)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖deriv (actualHartreeMatchedSpectralCorrectedValue K a b F U DU d) r -
      deriv (actualOriginMatchedKummerValue K a b F U DU) r‖ ≤
      (b + 1) * G * (1 + (D + 1) * G * b ^ 2) * (‖d‖ * H) +
      2 * (D + 1) * G ^ 2 * (‖d‖ * H) * b ^ 2 := by
  let u : ℝ → ℂ := actualOriginMatchedKummerValue K a b F U DU
  let q : ℝ → ℂ := actualHartreeMatchedSpectralFirstSource K a b F U DU d
  let w₁ : ℝ → ℂ := actualOriginMatchedKummerValue K a b q 0 0
  have hU :=
    actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb F hF U DU
  have hQcont : ∀ x ∈ Ioo (0 : ℝ) scale, ContinuousAt q x := by
    intro x hx
    change ContinuousAt (fun y : ℝ => d * u y) x
    exact continuousAt_const.mul ((hU x hx).1.continuousAt)
  have hrPos : r ∈ Ioo (0 : ℝ) scale :=
    ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  have hWu : HasDerivAt u
      (actualOriginMatchedKummerSlope K a b F U DU r) r :=
    (hU r hrPos).1
  have hW₁ : HasDerivAt w₁
      (actualOriginMatchedKummerSlope K a b q 0 0 r) r :=
    (actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb q hQcont 0 0 r hrPos).1
  have hCorrected :
      HasDerivAt
        (actualHartreeMatchedSpectralCorrectedValue K a b F U DU d)
        (actualOriginMatchedKummerSlope K a b F U DU r -
          actualOriginMatchedKummerSlope K a b q 0 0 r) r := by
    change HasDerivAt (fun x => u x - w₁ x) _ r
    exact hWu.sub hW₁
  have hGap :
      deriv (actualHartreeMatchedSpectralCorrectedValue
          K a b F U DU d) r - deriv u r = -deriv w₁ r := by
    rw [hCorrected.deriv, hWu.deriv, hW₁.deriv]
    abel
  have hFirst :=
    actual_Hartree_original_matched_spectral_unweighted_C1_no_left_radius
      K a b D G H ha hab hb hD hG hH hcoeff hbound
      F hF U DU d hProfile r hr
  rw [show deriv (actualOriginMatchedKummerValue K a b F U DU) r =
    deriv u r from rfl, hGap, norm_neg]
  exact hFirst

end HBL.TypeIIDynamicSelection
