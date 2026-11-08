import HBL.TypeIIDynamicSelection.ActualHartreeMatchedRegularJetNoRadiusLoss
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedOriginalSourceWeightedSpectral
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralUpperFluxWeighted
import Mathlib.Tactic

/-!
# Hartree matched Kummer weighted profile without a singular regular-jet constant

The exact original Cramer compatibility condition kills the singular
homogeneous mode. The true inverse-square source gives the original
no-left-radius-loss Green field. The remaining regular homogeneous
component is quantitatively bounded from the original Fredholm left
Cauchy jet using the exact Wronskian cancellation. Crucially, the regular
coefficient estimate uses ONLY the bounded origin IVP pair y,dy,x;
no unweighted bound on y/r or dy/r-y/r² enters that term.

This closes a source + Cramer regular jet to weighted matched first
profile to quadratic spectral error chain on the same Kummer interval.
The inhomogeneous Green contribution still contains its explicit
OriginBasisOn constant, potentially moving-radius-dependent. No
independent profile bound is postulated, and no nonlinear PDE time
order, outer interface repair, or Type-II exponent is claimed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_matched_source_and_uniform_regular_jet_weighted
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G Q : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hQ : 0 ≤ Q)
    (hK : OriginBasisOn K a b C)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ) (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ Q / x ^ 2)
    (U DU : ℂ)
    (hCompatible : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖(r : ℂ) * actualOriginMatchedKummerValue K a b F U DU r‖ ≤
      b * ((2 * C ^ 2 * (b - a)) * Q) +
        G ^ 2 * (a * ‖DU‖ + (a + 1) * ‖U‖) := by
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
  have hrpos : 0 < r := ha.trans_le hr.1
  have hnormr : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  have hb0 : 0 ≤ b := ha.le.trans hab
  have hGreenWeighted :
      ‖(r : ℂ) * originGreenValue K a b F r‖ ≤
        b * ((2 * C ^ 2 * (b - a)) * Q) := by
    rw [norm_mul, hnormr]
    exact mul_le_mul hr.2 hGreenValue (norm_nonneg _) hb0
  have hRegularWeighted :=
    actual_Hartree_matched_regular_part_weighted_no_radius_loss
      K a b G ha hab hb hG hbound F U DU r hr
  have hSplit :
      (r : ℂ) * actualOriginMatchedKummerValue K a b F U DU r =
        (r : ℂ) * originGreenValue K a b F r +
          (r : ℂ) * (actualOriginMatchedRegularCoeff K a b F U DU *
            originPhysicalValue K.x r) := by
    unfold actualOriginMatchedKummerValue
    rw [hZeroSing]
    ring
  rw [hSplit]
  exact (norm_add_le _ _).trans (add_le_add hGreenWeighted hRegularWeighted)

/-- The same original source and Fredholm Cramer left jet produce the
weighted first profile needed by the exact zero-left-jet spectral
quadratic residual, without a separately postulated weighted H. -/
theorem actual_Hartree_matched_source_regular_jet_quadratic_spectral_error
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G Q : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hQ : 0 ≤ Q)
    (hK : OriginBasisOn K a b C)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ) (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ Q / x ^ 2)
    (U DU d : ℂ)
    (hCompatible : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖d * actualOriginMatchedKummerValue K a b
        (actualHartreeMatchedSpectralFirstSource K a b F U DU d) 0 0 r‖ ≤
      (2 * G ^ 2 * (b - a)) *
        (‖d‖ ^ 2 * (b * ((2 * C ^ 2 * (b - a)) * Q) +
          G ^ 2 * (a * ‖DU‖ + (a + 1) * ‖U‖))) / r := by
  let H : ℝ :=
    b * ((2 * C ^ 2 * (b - a)) * Q) +
      G ^ 2 * (a * ‖DU‖ + (a + 1) * ‖U‖)
  have hH : 0 ≤ H := by
    dsimp [H]
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hb0 : 0 ≤ b := ha.le.trans hab
    positivity
  have hProfile : ∀ x ∈ Icc a b,
      ‖(x : ℂ) * actualOriginMatchedKummerValue K a b F U DU x‖ ≤ H := by
    intro x hx
    exact actual_Hartree_matched_source_and_uniform_regular_jet_weighted
      K a b C G Q ha hab hb hC hG hQ hK hbound F hF U DU
      hCompatible x hx
  have hOrig : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G := by
    intro x hx
    exact ⟨(hbound x hx).1, (hbound x hx).2.2⟩
  exact actual_Hartree_matched_spectral_quadratic_defect_weighted
    K a b C G H ha hab hb hG hH hK hOrig
      F U DU d hProfile r hr


/-- The outgoing obstruction of the exact left-C1-preserving spectral
correction is derived from the SAME original source and Cramer left jet.
There is no independent weighted profile envelope. The obstruction is
quantitatively bounded, not falsely set equal to zero; its repair in the
full time-dependent physical field still requires the true PDE gain. -/
theorem actual_Hartree_matched_source_regular_jet_spectral_outgoing_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G Q : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hQ : 0 ≤ Q)
    (hK : OriginBasisOn K a b C)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ) (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ Q / x ^ 2)
    (U DU d : ℂ)
    (hCompatible : actualMomentLockedIntervalObstruction K a b F U DU = 0) :
    ‖actualMomentLockedIntervalObstruction K a b
        (actualHartreeMatchedSpectralFirstSource K a b F U DU d) 0 0‖ ≤
      G * (‖d‖ * (b * ((2 * C ^ 2 * (b - a)) * Q) +
        G ^ 2 * (a * ‖DU‖ + (a + 1) * ‖U‖))) * (b - a) := by
  let H : ℝ :=
    b * ((2 * C ^ 2 * (b - a)) * Q) +
      G ^ 2 * (a * ‖DU‖ + (a + 1) * ‖U‖)
  have hH : 0 ≤ H := by
    dsimp [H]
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hb0 : 0 ≤ b := ha.le.trans hab
    positivity
  have hProfile : ∀ x ∈ Icc a b,
      ‖actualOriginMatchedKummerValue K a b F U DU x‖ ≤ H / x := by
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx.1
    have hnormx : ‖(x : ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
    have hWeighted :=
      actual_Hartree_matched_source_and_uniform_regular_jet_weighted
        K a b C G Q ha hab hb hC hG hQ hK hbound
        F hF U DU hCompatible x hx
    rw [norm_mul, hnormx] at hWeighted
    apply (le_div_iff₀ hxpos).2
    simpa only [mul_comm] using hWeighted
  exact actual_Hartree_matched_spectral_upper_obstruction_regularized_bound
    K a b G H ha hab hb hG hH
    (fun x hx => ⟨(hbound x hx).1, (hbound x hx).2.2⟩)
    F U DU d hProfile

end HBL.TypeIIDynamicSelection
