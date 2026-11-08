import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer
import HBL.KummerOriginGreen.UniformBound
import Mathlib.Tactic

/-!
# Quantitative inner bound for the SAME source-selected matched Kummer solution

Once the original moment-locked compatibility obstruction is canceled,
the singular homogeneous coefficient is exactly zero. The complete
interior Green--regular Kummer field is then bounded by its genuine
inhomogeneous source F and the ORIGINAL left Cauchy jet U, DU, not an
arbitrary new homogeneous amplitude or an independently prescribed
outer-boundary jet.

The source norm on a fixed annulus and the original basis constant are
visible. A uniform estimate for moving annuli or an O(s^(-9/4))
whole-Hartree residual is NOT claimed here. This closes the correct
fixed-annulus source-to-interior-field norm interface needed when
estimating a globally C1 spliced physical packet.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Full matched value and slope on the interval, not only the upper jet.
The singular coefficient has been removed by the SAME true compatibility
equation, and the complete original Green source remains in the bound. -/
theorem actual_Hartree_matched_Kummer_interior_source_and_regular_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M)
    (U DU : ℂ)
    (hzero : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖actualOriginMatchedKummerValue K a b F U DU r‖ +
      ‖actualOriginMatchedKummerSlope K a b F U DU r‖ ≤
      (2 * C ^ 3 * (b - a)) * M +
        2 * C * ‖actualOriginMatchedRegularCoeff K a b F U DU‖ := by
  have hzeroSing :
      actualOriginMatchedSingularCoeff K a b F U DU = 0 :=
    (actual_origin_matched_Kummer_singular_eq_obstruction K hK hab F U DU).trans
      hzero
  have hGreen :=
    originGreen_value_slope_norm_le K a b C M hC hM hK F hF hr
  rcases hK r hr with
    ⟨_, _, _, _, _, _, _, _, hx, hdx, _⟩
  let q := actualOriginMatchedRegularCoeff K a b F U DU
  have hValue :
      ‖actualOriginMatchedKummerValue K a b F U DU r‖ ≤
        ‖originGreenValue K a b F r‖ + C * ‖q‖ := by
    calc
      _ = ‖originGreenValue K a b F r +
            q * originPhysicalValue K.x r‖ := by
        simp [actualOriginMatchedKummerValue, q, hzeroSing]
      _ ≤ ‖originGreenValue K a b F r‖ +
          ‖q * originPhysicalValue K.x r‖ := norm_add_le _ _
      _ = ‖originGreenValue K a b F r‖ +
          ‖q‖ * ‖originPhysicalValue K.x r‖ := by rw [norm_mul]
      _ ≤ ‖originGreenValue K a b F r‖ + ‖q‖ * C := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hx (norm_nonneg q)) _
      _ = _ := by ring
  have hSlope :
      ‖actualOriginMatchedKummerSlope K a b F U DU r‖ ≤
        ‖originGreenSlope K a b F r‖ + C * ‖q‖ := by
    calc
      _ = ‖originGreenSlope K a b F r +
            q * originPhysicalSlope K.x K.dx r‖ := by
        simp [actualOriginMatchedKummerSlope, q, hzeroSing]
      _ ≤ ‖originGreenSlope K a b F r‖ +
          ‖q * originPhysicalSlope K.x K.dx r‖ := norm_add_le _ _
      _ = ‖originGreenSlope K a b F r‖ +
          ‖q‖ * ‖originPhysicalSlope K.x K.dx r‖ := by rw [norm_mul]
      _ ≤ ‖originGreenSlope K a b F r‖ + ‖q‖ * C := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hdx (norm_nonneg q)) _
      _ = _ := by ring
  change ‖actualOriginMatchedKummerValue K a b F U DU r‖ +
    ‖actualOriginMatchedKummerSlope K a b F U DU r‖ ≤
      (2 * C ^ 3 * (b - a)) * M + 2 * C * ‖q‖
  linarith [hGreen, hValue, hSlope]

/-- The original left Cauchy jet also bounds the regular coefficient:
the normalized Wronskian is read from the actual origin pair. -/
theorem actual_Hartree_matched_Kummer_regular_coefficient_from_left_jet
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C : ℝ) (hC : 0 ≤ C)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ) (U DU : ℂ) :
    ‖actualOriginMatchedRegularCoeff K a b F U DU‖ ≤
      C ^ 2 * (‖U‖ + ‖DU‖) := by
  rcases hK a ⟨le_refl a, hab⟩ with
    ⟨_, _, _, _, _, _, hY, hDY, _, _, hW⟩
  have hNumerator :
      ‖originPhysicalValue K.y a * DU -
          originPhysicalSlope K.y K.dy a * U‖ ≤
        C * (‖U‖ + ‖DU‖) := by
    calc
      _ ≤ ‖originPhysicalValue K.y a * DU‖ +
          ‖originPhysicalSlope K.y K.dy a * U‖ := norm_sub_le _ _
      _ = ‖originPhysicalValue K.y a‖ * ‖DU‖ +
          ‖originPhysicalSlope K.y K.dy a‖ * ‖U‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ C * ‖DU‖ + C * ‖U‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hY (norm_nonneg DU))
          (mul_le_mul_of_nonneg_right hDY (norm_nonneg U))
      _ = _ := by ring
  rw [actual_origin_matched_Kummer_regular_coefficient, div_eq_mul_inv,
    norm_mul]
  calc
    _ ≤ (C * (‖U‖ + ‖DU‖)) *
        ‖(originGreenWronskian K a)⁻¹‖ :=
      mul_le_mul_of_nonneg_right hNumerator (norm_nonneg _)
    _ ≤ (C * (‖U‖ + ‖DU‖)) * C :=
      mul_le_mul_of_nonneg_left hW
        (mul_nonneg hC (add_nonneg (norm_nonneg U) (norm_nonneg DU)))
    _ = _ := by ring

/-- The complete interior Green--Kummer value and slope gain are supplied
by the SAME source F and SAME actual left Fredholm jet. No free regular
coefficient and no separately assumed interior envelope remain. -/
theorem actual_Hartree_matched_Kummer_interior_from_source_and_left_jet
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M)
    (U DU : ℂ)
    (hzero : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖actualOriginMatchedKummerValue K a b F U DU r‖ +
      ‖actualOriginMatchedKummerSlope K a b F U DU r‖ ≤
      (2 * C ^ 3) * ((b - a) * M + ‖U‖ + ‖DU‖) := by
  have hFull :=
    actual_Hartree_matched_Kummer_interior_source_and_regular_bound
      K a b C M hC hM hK hab F hF U DU hzero r hr
  have hCoeff :=
    actual_Hartree_matched_Kummer_regular_coefficient_from_left_jet
      K a b C hC hK hab F U DU
  have hC2 : 0 ≤ 2 * C := by positivity
  calc
    _ ≤ (2 * C ^ 3 * (b - a)) * M +
        2 * C * ‖actualOriginMatchedRegularCoeff K a b F U DU‖ := hFull
    _ ≤ (2 * C ^ 3 * (b - a)) * M +
        2 * C * (C ^ 2 * (‖U‖ + ‖DU‖)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hCoeff hC2) _
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
