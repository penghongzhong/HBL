import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftRegularizedVolterra
import Mathlib.Tactic

/-!
# True zero-left Cramer spectral Volterra: weighted VALUE AND radial SLOPE

The original physical Kummer singular mode Y=y/r is not uniform as the
left interface r0 tends to zero. The genuine zero-left-jet Cramer correction,
however, has a precise cancellation of the singular A(r0) coefficient.

For the same original inverse-linear source |F(r)| <= M/r,
the regularized IVP pair and its first derivatives are uniformly
bounded by G on [0,scale]. The ORIGINAL Kummer Wronskian source moments
therefore give two simultaneous radius-uniform estimates:
  |r u1(r)| <= 2 G² (b-a) M,
  |r² u1'(r)| <= 2(b+1) G² (b-a) M.

The derivative is the actual original Kummer slope; the identity uses the
full Cramer coefficient, not an abstract differentiation assumption.
This controls the NEW matching C¹ upper jet of the spectral correction
without inserting any inverse left matching radius or assumed Type-II rate.

The source-to-M producer and time/space residual still come from the
original nonlocal Hartree physical orbit, not from this bound alone.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- A second exact cancellation: the weighted physical radial derivative
only contains the regularized origin IVP modes and their derivatives. -/
theorem actual_Hartree_zero_left_Kummer_regularized_Volterra_slope_identity
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) (r : ℝ) (hr : r ∈ Icc a b) :
    (r : ℂ) ^ 2 * actualOriginMatchedKummerSlope K a b F 0 0 r =
      ((r : ℂ) * K.dy r - K.y r) *
        (originGreenCoeffA K b F r - originGreenCoeffA K b F a) +
      ((r : ℂ) * K.dx r - K.x r) *
        originGreenCoeffB K a F r := by
  have hr0 : 0 < r := ha.trans_le hr.1
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hSing :
      actualOriginMatchedSingularCoeff K a b F 0 0 =
        -originGreenCoeffA K b F a := by
    rw [actual_origin_matched_Kummer_singular_eq_obstruction
      K hK hab F 0 0]
    unfold actualMomentLockedIntervalObstruction actualOriginOutgoingTrace
    simp
  have hReg : actualOriginMatchedRegularCoeff K a b F 0 0 = 0 := by
    rw [actual_origin_matched_Kummer_regular_coefficient K a b F 0 0]
    simp
  unfold actualOriginMatchedKummerSlope originGreenSlope
  rw [hSing, hReg]
  simp only [zero_mul, add_zero]
  unfold originPhysicalSlope
  field_simp [hrC]
  ring

/-- Actual first radial Cauchy derivative bound. The constant depends on
only the globally bounded REGULARIZED IVP pair, not the singular basis
constant OriginBasisOn.C or any negative power of a. -/
theorem actual_Hartree_zero_left_Kummer_regularized_Volterra_slope_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G M : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ scale) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M / x)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖(r : ℂ) ^ 2 * actualOriginMatchedKummerSlope K a b F 0 0 r‖ ≤
      2 * (b + 1) * G ^ 2 * (b - a) * M := by
  have hr0 : 0 < r := ha.trans_le hr.1
  have hb0 : 0 ≤ b := (ha.trans_le hab).le
  have hModes := hbound r ⟨hr0.le, hr.2.trans hb⟩
  have hPairs : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G := by
    intro x hx
    exact ⟨(hbound x hx).1, (hbound x hx).2.2.1⟩
  have hCoeffs (x : ℝ) (hx : x ∈ Icc a b) :=
    originGreen_inverse_linear_coefficients_regularized_uniform
      K a b G M ha hab hb hG hM hPairs F hF x hx
  have hAr := (hCoeffs r hr).1
  have hAa := (hCoeffs a ⟨le_refl a, hab⟩).1
  have hBr := (hCoeffs r hr).2
  have hJ : 0 ≤ (b + 1) * G := by positivity
  have hMode (p dp : ℝ → ℂ)
      (hp : ‖p r‖ ≤ G) (hdp : ‖dp r‖ ≤ G) :
      ‖(r : ℂ) * dp r - p r‖ ≤ (b + 1) * G := by
    calc
      _ ≤ ‖(r : ℂ) * dp r‖ + ‖p r‖ := norm_sub_le _ _
      _ = r * ‖dp r‖ + ‖p r‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      _ ≤ r * G + G :=
        add_le_add (mul_le_mul_of_nonneg_left hdp hr0.le) hp
      _ ≤ b * G + G :=
        add_le_add_left
          (mul_le_mul_of_nonneg_right hr.2 hG) G
      _ = (b + 1) * G := by ring
  have hY : ‖(r : ℂ) * K.dy r - K.y r‖ ≤ (b + 1) * G :=
    hMode K.y K.dy hModes.1 hModes.2.1
  have hX : ‖(r : ℂ) * K.dx r - K.x r‖ ≤ (b + 1) * G :=
    hMode K.x K.dx hModes.2.2.1 hModes.2.2.2
  have hId := actual_Hartree_zero_left_Kummer_regularized_Volterra_slope_identity
    K a b C ha hab hK F r hr
  rw [hId]
  calc
    ‖((r : ℂ) * K.dy r - K.y r) *
        (originGreenCoeffA K b F r - originGreenCoeffA K b F a) +
      ((r : ℂ) * K.dx r - K.x r) *
        originGreenCoeffB K a F r‖ ≤
      ‖(r : ℂ) * K.dy r - K.y r‖ *
        (‖originGreenCoeffA K b F r‖ + ‖originGreenCoeffA K b F a‖) +
      ‖(r : ℂ) * K.dx r - K.x r‖ * ‖originGreenCoeffB K a F r‖ := by
      calc
        _ ≤ ‖((r : ℂ) * K.dy r - K.y r) *
                (originGreenCoeffA K b F r - originGreenCoeffA K b F a)‖ +
              ‖((r : ℂ) * K.dx r - K.x r) *
                originGreenCoeffB K a F r‖ := norm_add_le _ _
        _ = ‖(r : ℂ) * K.dy r - K.y r‖ *
              ‖originGreenCoeffA K b F r - originGreenCoeffA K b F a‖ +
            ‖(r : ℂ) * K.dx r - K.x r‖ *
              ‖originGreenCoeffB K a F r‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖(r : ℂ) * K.dy r - K.y r‖ *
              (‖originGreenCoeffA K b F r‖ + ‖originGreenCoeffA K b F a‖) +
            ‖(r : ℂ) * K.dx r - K.x r‖ *
              ‖originGreenCoeffB K a F r‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
            (le_refl _)
    _ ≤ ((b + 1) * G) *
          ((G * M) * (b - r) + (G * M) * (b - a)) +
        ((b + 1) * G) * ((G * M) * (r - a)) := by
      apply add_le_add
      · exact mul_le_mul hY (add_le_add hAr hAa)
          (add_nonneg (norm_nonneg _) (norm_nonneg _)) hJ
      · exact mul_le_mul hX hBr (norm_nonneg _) hJ
    _ = 2 * (b + 1) * G ^ 2 * (b - a) * M := by ring

/-- Both physical C¹ coordinates of the literal zero-left matched Green
response are controlled by the same inverse-linear source, at every radius. -/
theorem actual_Hartree_zero_left_Kummer_regularized_Volterra_weighted_C1_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G M : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ scale) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M / x)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖(r : ℂ) * actualOriginMatchedKummerValue K a b F 0 0 r‖ +
      ‖(r : ℂ) ^ 2 * actualOriginMatchedKummerSlope K a b F 0 0 r‖ ≤
      2 * (b + 2) * G ^ 2 * (b - a) * M := by
  have hPairs : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G := by
    intro x hx
    exact ⟨(hbound x hx).1, (hbound x hx).2.2.1⟩
  have hVal :=
    actual_Hartree_zero_left_Kummer_regularized_Volterra_value_bound
      K a b C G M ha hab hb hG hM hK hPairs F hF r hr
  have hSlope :=
    actual_Hartree_zero_left_Kummer_regularized_Volterra_slope_bound
      K a b C G M ha hab hb hG hM hK hbound F hF r hr
  calc
    _ ≤ 2 * G ^ 2 * (b - a) * M +
        2 * (b + 1) * G ^ 2 * (b - a) * M := add_le_add hVal hSlope
    _ = 2 * (b + 2) * G ^ 2 * (b - a) * M := by ring

end HBL.TypeIIDynamicSelection
