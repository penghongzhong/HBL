import HBL.KummerOriginGreen.InverseLinearRegularMomentDifference
import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftRegularizedVolterraSlope
import HBL.KummerOriginBasis.RegularDerivativeBound
import Mathlib.Tactic

/-!
# Genuine zero-left Kummer Volterra: UNWEIGHTED radial derivative without 1/r0

The prior bound r²|u'(r)| <= E is insufficient to infer the original
three-dimensional radial Hdot1 energy uniformly as the moving lower
matching radius r0 tends to zero. Here the entire Cramer cancellation
is retained through the original Green integral before estimating.

For the ORIGINAL inverse-linear source |F(s)|<=M/s, the regular outgoing
density enjoys the extra factor s from X(s)=x(s)/s=O(1).
The exact A(r)-A(a) coefficient gains a factor r(r-a).
The regular IVP identity r dx(r)-x(r)=O(r³) gives another gain in
the coefficient B channel. Consequently the physical slope of the
ACTUAL zero-left-jet matched Kummer field is bounded in the
UNWEIGHTED norm, with no inverse moving-left-radius a.

No rate of a(t), arbitrary time-small envelope or Type-II blowup
exponent is assumed. The genuine Hartree source-to-M producer remains
a separate requirement for the final PDE.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Exact unweighted C1 bound for the original Cramer zero-left response
to an inverse-linear physical source on a moving small Kummer annulus. -/
theorem actual_Hartree_zero_left_Kummer_Volterra_unweighted_slope_no_left_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C D G M : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ)
    (hFCont : ∀ x ∈ Ioo 0 scale, ContinuousAt F x)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M / x)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖actualOriginMatchedKummerSlope K a b F 0 0 r‖ ≤
      ((b + 1) * G * (1 + (D + 1) * G * b ^ 2) * M +
        2 * (D + 1) * G ^ 2 * M * b ^ 2) := by
  let J : ℝ := 1 + (D + 1) * G * b ^ 2
  let E : ℝ := (b + 1) * G * J * M +
    2 * (D + 1) * G ^ 2 * M * b ^ 2
  have hr0 : 0 < r := ha.trans_le hr.1
  have hb0 : 0 ≤ b := (ha.trans_le hab).le
  have hrscale : r ∈ Icc 0 scale :=
    ⟨hr0.le, hr.2.trans hb.le⟩
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hGM : 0 ≤ G * M := mul_nonneg hG hM
  have hJM : 0 ≤ J * M := mul_nonneg hJ hM
  have hBM : 0 ≤ b + 1 := by linarith
  have hYconst : 0 ≤ (b + 1) * G := mul_nonneg hBM hG
  have hXconst : 0 ≤ 2 * (D + 1) * G := by positivity
  have hXconstFull : 0 ≤ 2 * (D + 1) * G ^ 2 * M := by positivity
  have hModes := hbound r hrscale
  have hY : ‖(r : ℂ) * K.dy r - K.y r‖ ≤ (b + 1) * G := by
    calc
      _ ≤ ‖(r : ℂ) * K.dy r‖ + ‖K.y r‖ := norm_sub_le _ _
      _ = r * ‖K.dy r‖ + ‖K.y r‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      _ ≤ r * G + G :=
        add_le_add (mul_le_mul_of_nonneg_left hModes.2.1 hr0.le) hModes.1
      _ ≤ b * G + G :=
        by
          have hMul : r * G ≤ b * G := mul_le_mul_of_nonneg_right hr.2 hG
          linarith
      _ = (b + 1) * G := by ring
  have hJet :=
    origin_kummer_regular_jet_bound K D G hD hG hcoeff hbound r hrscale
  have hX : ‖(r : ℂ) * K.dx r - K.x r‖ ≤
      (2 * (D + 1) * G) * r ^ 3 := by
    have hEq : (r : ℂ) * K.dx r - K.x r =
        (r : ℂ) * (K.dx r - 1) -
        (K.x r - (r : ℂ)) := by ring
    rw [hEq]
    calc
      _ ≤ ‖(r : ℂ) * (K.dx r - 1)‖ +
          ‖K.x r - (r : ℂ)‖ := norm_sub_le _ _
      _ = r * ‖K.dx r - 1‖ + ‖K.x r - (r : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      _ ≤ r * ((D + 1) * G * r ^ 2) +
          (D + 1) * G * r ^ 3 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hJet.2 hr0.le) hJet.1
      _ = (2 * (D + 1) * G) * r ^ 3 := by ring
  have hA :=
    originGreen_inverse_linear_regular_A_moment_difference_radius_gain
      K a b C D G M ha hab hb hD hG hM hK hcoeff hbound
      F hFCont hF r hr
  have hA2 :
      ‖originGreenCoeffA K b F r -
        originGreenCoeffA K b F a‖ ≤ (J * M) * r ^ 2 := by
    have hdist : r - a ≤ r := by linarith
    calc
      _ ≤ ((J * M) * r) * (r - a) := by
        simpa only [J, mul_assoc] using hA
      _ ≤ ((J * M) * r) * r :=
        mul_le_mul_of_nonneg_left hdist
          (mul_nonneg hJM hr0.le)
      _ = (J * M) * r ^ 2 := by ring
  have hPair : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G := by
    intro x hx
    exact ⟨(hbound x hx).1, (hbound x hx).2.2.1⟩
  have hB := (originGreen_inverse_linear_coefficients_regularized_uniform
    K a b G M ha hab hb.le hG hM hPair F hF r hr).2
  have hB2 : ‖originGreenCoeffB K a F r‖ ≤ (G * M) * r := by
    have hdist : r - a ≤ r := by linarith
    exact hB.trans (mul_le_mul_of_nonneg_left hdist hGM)
  have hrSq : r ^ 2 ≤ b ^ 2 :=
    pow_le_pow_left₀ hr0.le hr.2 2
  have hr4 : r ^ 4 ≤ b ^ 2 * r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrSq) (sq_nonneg r)]
  have hId :=
    actual_Hartree_zero_left_Kummer_regularized_Volterra_slope_identity
      K a b C ha hab hK F r hr
  have hScaled :
      ‖(r : ℂ) ^ 2 * actualOriginMatchedKummerSlope K a b F 0 0 r‖ ≤
      E * r ^ 2 := by
    rw [hId]
    calc
      ‖((r : ℂ) * K.dy r - K.y r) *
          (originGreenCoeffA K b F r -
            originGreenCoeffA K b F a) +
        ((r : ℂ) * K.dx r - K.x r) *
          originGreenCoeffB K a F r‖ ≤
        ‖(r : ℂ) * K.dy r - K.y r‖ *
          ‖originGreenCoeffA K b F r -
            originGreenCoeffA K b F a‖ +
        ‖(r : ℂ) * K.dx r - K.x r‖ *
          ‖originGreenCoeffB K a F r‖ := by
            simpa only [norm_mul] using
              (norm_add_le
                (((r : ℂ) * K.dy r - K.y r) *
                  (originGreenCoeffA K b F r -
                    originGreenCoeffA K b F a))
                (((r : ℂ) * K.dx r - K.x r) *
                  originGreenCoeffB K a F r))
      _ ≤ ((b + 1) * G) * ((J * M) * r ^ 2) +
          ((2 * (D + 1) * G) * r ^ 3) *
            ((G * M) * r) := by
          exact add_le_add
            (mul_le_mul hY hA2 (norm_nonneg _)
              hYconst)
            (mul_le_mul hX hB2 (norm_nonneg _)
              (mul_nonneg hXconst (pow_nonneg hr0.le 3)))
      _ = ((b + 1) * G * J * M) * r ^ 2 +
          (2 * (D + 1) * G ^ 2 * M) * r ^ 4 := by ring
      _ ≤ ((b + 1) * G * J * M) * r ^ 2 +
          (2 * (D + 1) * G ^ 2 * M) * (b ^ 2 * r ^ 2) :=
        by
          have hMul := mul_le_mul_of_nonneg_left hr4 hXconstFull
          linarith
      _ = E * r ^ 2 := by dsimp [E]; ring
  have hNorm :
      ‖(r : ℂ) ^ 2 * actualOriginMatchedKummerSlope K a b F 0 0 r‖ =
        r ^ 2 * ‖actualOriginMatchedKummerSlope K a b F 0 0 r‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hE :
      r ^ 2 * ‖actualOriginMatchedKummerSlope K a b F 0 0 r‖ ≤
        r ^ 2 * E := by
    rw [← hNorm]
    calc
      _ ≤ E * r ^ 2 := hScaled
      _ = r ^ 2 * E := by ring
  have hFinal :
      ‖actualOriginMatchedKummerSlope K a b F 0 0 r‖ ≤ E :=
    (mul_le_mul_iff_of_pos_left (pow_pos hr0 2)).mp hE
  simpa only [E, J, mul_assoc] using hFinal

end HBL.TypeIIDynamicSelection
