import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftRegularizedVolterraSlope
import HBL.KummerOriginBasis.RegularDerivativeBound
import HBL.KummerOriginGreen.InverseSquareSourceNoLeftRadiusLoss
import Mathlib.Tactic

/-!
# The zero-left inverse-square Kummer Volterra radial-energy core

This is ONLY a source-class lemma. The inverse-square source bound and
regular B-channel moment must be supplied from the same genuine Hartree
Riesz/Cramer selected source in the later physical theorem.
Exact regular-mode Wronskian cancellation yields a uniformly weighted
radial-energy slope with no 1/a term as the left interface shrinks.
No time gain or Type-II rate is assumed here.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The 3D energy-weighted radial slope of the zero-left exact Kummer
Cramer correction: the A-moment difference grows only as (r-a) and
the B-moment is bounded by its native source producer. -/
theorem actual_Hartree_zero_left_inverse_square_energy_slope_core
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B a Q T : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (ha : 0 < a) (hab : a ≤ B) (hBscale : B < scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hQ : 0 ≤ Q) (hT : 0 ≤ T)
    (F : ℝ → ℂ)
    (hFI : IntervalIntegrable F volume a B)
    (hEnvelope : ∀ x ∈ Icc a B, ‖F x‖ ≤ Q / x ^ 2)
    (hBcoeff : ∀ x ∈ Icc a B, ‖originGreenCoeffB K a F x‖ ≤ T)
    (r : ℝ) (hr : r ∈ Icc a B) :
    let J : ℝ := 1 + (D + 1) * G * B ^ 2
    ‖(r : ℂ) * actualOriginMatchedKummerSlope K a B F 0 0 r‖ ≤
      (B + 1) * G * J * Q + 2 * (D + 1) * G * B ^ 2 * T := by
  dsimp only
  let J : ℝ := 1 + (D + 1) * G * B ^ 2
  let E : ℝ := (B + 1) * G * J * Q +
    2 * (D + 1) * G * B ^ 2 * T
  have hr0 : 0 < a := ha
  have hrp : 0 < r := hr0.trans_le hr.1
  have hBp : 0 ≤ B := (hr0.trans_le hab).le
  have hrscale : r ∈ Icc 0 scale := ⟨hrp.le, hr.2.trans hBscale.le⟩
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hJQ : 0 ≤ J * Q := mul_nonneg hJ hQ
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hYconst : 0 ≤ (B + 1) * G := by positivity
  have hXconst : 0 ≤ 2 * (D + 1) * G := by positivity
  have hXFull : 0 ≤ 2 * (D + 1) * G * T := by positivity
  let Cbasis : ℝ := G * (1 / a + 1 / a ^ 2) + B ^ 2 + 1
  have hK : OriginBasisOn K a B Cbasis :=
    origin_kummer_annulus_bound K a B G
      hr0 hBscale hG hbound
  let q : ℝ → ℂ := originGreenSourceA K F
  have hIq : IntervalIntegrable q volume a B := by
    simpa only [q] using
      (actual_origin_Green_source_integrability K hK hab F hFI).1
  have hIar : IntervalIntegrable q volume a r :=
    hIq.mono_set (by
      rw [uIcc_of_le hr.1, uIcc_of_le hab]
      exact Icc_subset_Icc_right hr.2)
  have hIrb : IntervalIntegrable q volume r B :=
    hIq.mono_set (by
      rw [uIcc_of_le hr.2, uIcc_of_le hab]
      exact Icc_subset_Icc_left hr.1)
  have hAdd := intervalIntegral.integral_add_adjacent_intervals hIar hIrb
  have hDifference :
      originGreenCoeffA K B F r -
        originGreenCoeffA K B F a =
        -(∫ x in a..r, q x) := by
    change (∫ x in r..B, q x) -
      (∫ x in a..B, q x) =
        -(∫ x in a..r, q x)
    rw [← hAdd]
    abel
  have hDensity (x : ℝ) (hx : x ∈ Icc a r) :
      ‖q x‖ ≤ J * Q := by
    have hxB : x ∈ Icc a B := ⟨hx.1, hx.2.trans hr.2⟩
    have hxpos : 0 < x := hr0.trans_le hx.1
    have hxscale : x ∈ Icc 0 scale :=
      ⟨hxpos.le, hxB.2.trans hBscale.le⟩
    have hX : ‖originPhysicalValue K.x x‖ ≤ J := by
      simpa only [J] using
        (origin_kummer_regular_physical_bound K D G hD hG
          hBscale.le hcoeff hbound x ⟨hxpos, hxB.2⟩).1
    have hWr := originGreenWronskian_exact K hK hxB
    have hExp :
        ‖Complex.exp (-Complex.I * (x : ℂ) ^ 2 / 4)‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, Complex.mul_im, pow_two]
    have hInv : ‖(originGreenWronskian K x)⁻¹‖ = x ^ 2 := by
      rw [hWr, norm_inv, norm_mul, norm_pow, norm_inv,
        hExp, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hxpos]
      simp
    have hFQ : ‖F x‖ * x ^ 2 ≤ Q := by
      calc
        _ ≤ (Q / x ^ 2) * x ^ 2 :=
          mul_le_mul_of_nonneg_right (hEnvelope x hxB) (sq_nonneg x)
        _ = Q := by field_simp [hxpos.ne']
    change ‖originPhysicalValue K.x x * F x /
      originGreenWronskian K x‖ ≤ J * Q
    rw [div_eq_mul_inv, norm_mul, norm_mul, hInv]
    calc
      ‖originPhysicalValue K.x x‖ * ‖F x‖ * x ^ 2 =
        ‖originPhysicalValue K.x x‖ * (‖F x‖ * x ^ 2) := by ring
      _ ≤ J * Q :=
        mul_le_mul hX hFQ
          (mul_nonneg (norm_nonneg _) (sq_nonneg x)) hJ
  have hAIntegral :
      ‖∫ x in a..r, q x‖ ≤ (J * Q) * |r - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hr.1] at hx
    exact hDensity x ⟨hx.1.le, hx.2⟩
  have hA :
      ‖originGreenCoeffA K B F r -
        originGreenCoeffA K B F a‖ ≤
        (J * Q) * (r - a) := by
    rw [hDifference, norm_neg]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hr.1)] using hAIntegral
  have hA2 :
      ‖originGreenCoeffA K B F r -
        originGreenCoeffA K B F a‖ ≤
        (J * Q) * r := by
    have hdist : r - a ≤ r := by linarith
    exact hA.trans (mul_le_mul_of_nonneg_left hdist hJQ)
  have hB : ‖originGreenCoeffB K a F r‖ ≤ T := hBcoeff r hr
  have hModes := hbound r hrscale
  have hY :
      ‖(r : ℂ) * K.dy r - K.y r‖ ≤ (B + 1) * G := by
    calc
      _ ≤ ‖(r : ℂ) * K.dy r‖ + ‖K.y r‖ := norm_sub_le _ _
      _ = r * ‖K.dy r‖ + ‖K.y r‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
      _ ≤ r * G + G :=
        add_le_add (mul_le_mul_of_nonneg_left hModes.2.1 hrp.le)
          hModes.1
      _ ≤ B * G + G := by
        have hMul : r * G ≤ B * G :=
          mul_le_mul_of_nonneg_right hr.2 hG
        linarith
      _ = (B + 1) * G := by ring
  have hJet :=
    origin_kummer_regular_jet_bound K D G hD hG hcoeff hbound r hrscale
  have hX :
      ‖(r : ℂ) * K.dx r - K.x r‖ ≤
        (2 * (D + 1) * G) * r ^ 3 := by
    have hEq :
        (r : ℂ) * K.dx r - K.x r =
          (r : ℂ) * (K.dx r - 1) - (K.x r - (r : ℂ)) := by ring
    rw [hEq]
    calc
      _ ≤ ‖(r : ℂ) * (K.dx r - 1)‖ +
          ‖K.x r - (r : ℂ)‖ := norm_sub_le _ _
      _ = r * ‖K.dx r - 1‖ + ‖K.x r - (r : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
      _ ≤ r * ((D + 1) * G * r ^ 2) +
          (D + 1) * G * r ^ 3 :=
        add_le_add (mul_le_mul_of_nonneg_left hJet.2 hrp.le) hJet.1
      _ = (2 * (D + 1) * G) * r ^ 3 := by ring
  have hrSq : r ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hrp.le hr.2 2
  have hr3 : r ^ 3 ≤ B ^ 2 * r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrSq) hrp.le]
  have hId :=
    actual_Hartree_zero_left_Kummer_regularized_Volterra_slope_identity
      K a B Cbasis hr0 hab hK F r hr
  have hScaled :
      ‖(r : ℂ) ^ 2 *
        actualOriginMatchedKummerSlope K a B F 0 0 r‖ ≤
      E * r := by
    rw [hId]
    calc
      ‖((r : ℂ) * K.dy r - K.y r) *
          (originGreenCoeffA K B F r -
            originGreenCoeffA K B F a) +
        ((r : ℂ) * K.dx r - K.x r) *
          originGreenCoeffB K a F r‖ ≤
        ‖(r : ℂ) * K.dy r - K.y r‖ *
          ‖originGreenCoeffA K B F r -
            originGreenCoeffA K B F a‖ +
        ‖(r : ℂ) * K.dx r - K.x r‖ *
          ‖originGreenCoeffB K a F r‖ := by
          simpa only [norm_mul] using
            (norm_add_le
              (((r : ℂ) * K.dy r - K.y r) *
                (originGreenCoeffA K B F r -
                  originGreenCoeffA K B F a))
              (((r : ℂ) * K.dx r - K.x r) *
                originGreenCoeffB K a F r))
      _ ≤ ((B + 1) * G) * ((J * Q) * r) +
          ((2 * (D + 1) * G) * r ^ 3) * T := by
        exact add_le_add
          (mul_le_mul hY hA2 (norm_nonneg _) hYconst)
          (mul_le_mul hX hB (norm_nonneg _)
            (mul_nonneg hXconst (pow_nonneg hrp.le 3)))
      _ = ((B + 1) * G * J * Q) * r +
          (2 * (D + 1) * G * T) * r ^ 3 := by ring
      _ ≤ ((B + 1) * G * J * Q) * r +
          (2 * (D + 1) * G * T) * (B ^ 2 * r) := by
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left hr3 hXFull)
      _ = E * r := by dsimp [E]; ring
  have hNorm :
      ‖(r : ℂ) ^ 2 * actualOriginMatchedKummerSlope K a B F 0 0 r‖ =
      r * ‖(r : ℂ) * actualOriginMatchedKummerSlope K a B F 0 0 r‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrp]
    ring
  rw [hNorm] at hScaled
  have hBudget :
      r * ‖(r : ℂ) * actualOriginMatchedKummerSlope K a B F 0 0 r‖ ≤
      r * E := by
    calc
      _ ≤ E * r := hScaled
      _ = r * E := by ring
  have hFinal :
      ‖(r : ℂ) * actualOriginMatchedKummerSlope K a B F 0 0 r‖ ≤
      E := (mul_le_mul_iff_of_pos_left hrp).mp hBudget
  simpa only [E, J, mul_assoc] using hFinal

end HBL.TypeIIDynamicSelection
