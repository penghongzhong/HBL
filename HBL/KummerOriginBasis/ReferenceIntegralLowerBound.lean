import HBL.KummerOriginBasis.RegularDerivativeBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
The reference outgoing projection uses the ACTUAL origin-normalized Kummer
solution.  Its integral is quantitatively close to B^2/2, uniformly under
the real ODE bounds.  Nonvanishing is derived on an explicitly small fixed
interval; it is not imposed as a premise on an arbitrary annulus.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Profile.Kummer

/-- The actual bubble reference integral in the original origin gauge. -/
def originKummerReferenceIntegral {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (B : ℝ) : ℂ :=
  ∫ r in 0..B, K.x r * Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4)

private theorem reference_phase_bounds (r : ℝ) :
    ‖Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 ∧
    ‖Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4) - 1‖ ≤ r ^ 2 / 4 := by
  have heq : Complex.I * (r : ℂ) ^ 2 / 4 =
      Complex.I * ((r ^ 2 / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq]
  constructor
  · exact Complex.norm_exp_I_mul_ofReal _
  · have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := r ^ 2 / 4)
    rw [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (by positivity : 0 ≤ r ^ 2 / 4)] at h
    exact h

/-- The actual reference density differs from r by a cubic integrable error. -/
theorem origin_kummer_reference_density_error_bound {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G) :
    ∀ r ∈ Icc 0 R,
      ‖K.x r * Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4) - (r : ℂ)‖ ≤
        ((D + 1) * G + 1 / 4) * r ^ 3 := by
  intro r hr
  have hj := (origin_kummer_regular_jet_bound K D G hD hG hcoeff hbound r hr).1
  have hp := reference_phase_bounds r
  have heq : K.x r * Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4) - (r : ℂ) =
      (K.x r - (r : ℂ)) * Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4) +
        (r : ℂ) * (Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4) - 1) := by ring
  rw [heq]
  calc
    _ ≤ ‖(K.x r - (r : ℂ)) * Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4)‖ +
        ‖(r : ℂ) * (Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4) - 1)‖ :=
      norm_add_le _ _
    _ = ‖K.x r - (r : ℂ)‖ +
        r * ‖Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4) - 1‖ := by
      rw [norm_mul, norm_mul, hp.1, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr.1]
    _ ≤ (D + 1) * G * r ^ 3 + r * (r ^ 2 / 4) :=
      add_le_add hj (mul_le_mul_of_nonneg_left hp.2 hr.1)
    _ = ((D + 1) * G + 1 / 4) * r ^ 3 := by ring

/-- Quantitative comparison with the real positive leading integral B^2/2.
Both the density and its actual origin interval are retained. -/
theorem origin_kummer_reference_integral_error_bound {mu theta R B : ℝ}
    (K : OriginKummerPair mu theta R) (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 ≤ B) (hBR : B ≤ R)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G) :
    ‖originKummerReferenceIntegral K B - ((B ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      ((D + 1) * G + 1 / 4) * B ^ 4 / 4 := by
  have hxC : ContinuousOn K.x (Icc 0 R) :=
    fun r hr => (K.x_deriv r hr).continuousWithinAt
  have hpC : Continuous (fun r : ℝ =>
      Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4)) := by fun_prop
  have hfC : ContinuousOn (fun r : ℝ =>
      K.x r * Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4)) (Icc 0 B) :=
    (hxC.mono (Icc_subset_Icc_right hBR)).mul hpC.continuousOn
  have hfI : IntervalIntegrable (fun r : ℝ =>
      K.x r * Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4)) volume 0 B :=
    hfC.intervalIntegrable_of_Icc hB
  have hidC : Continuous (fun r : ℝ => (r : ℂ)) := by fun_prop
  have hidI : IntervalIntegrable (fun r : ℝ => (r : ℂ)) volume 0 B :=
    hidC.intervalIntegrable 0 B
  have hid : (∫ r in 0..B, (r : ℂ)) = ((B ^ 2 / 2 : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_ofReal, _root_.integral_id]
    norm_num
  have hdiff : originKummerReferenceIntegral K B - ((B ^ 2 / 2 : ℝ) : ℂ) =
      ∫ r in 0..B,
        K.x r * Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4) - (r : ℂ) := by
    unfold originKummerReferenceIntegral
    rw [intervalIntegral.integral_sub hfI hidI, hid]
  rw [hdiff]
  have hgC : Continuous (fun r : ℝ => ((D + 1) * G + 1 / 4) * r ^ 3) := by fun_prop
  have hgI : IntervalIntegrable
      (fun r : ℝ => ((D + 1) * G + 1 / 4) * r ^ 3) volume 0 B :=
    hgC.intervalIntegrable 0 B
  calc
    _ ≤ ∫ r in 0..B, ((D + 1) * G + 1 / 4) * r ^ 3 := by
      apply intervalIntegral.norm_integral_le_of_norm_le hB _ hgI
      filter_upwards with r hr
      exact origin_kummer_reference_density_error_bound K D G hD hG hcoeff hbound
        r ⟨hr.1.le, hr.2.trans hBR⟩
    _ = ((D + 1) * G + 1 / 4) * B ^ 4 / 4 := by
      rw [intervalIntegral.integral_const_mul, _root_.integral_pow]
      norm_num [mul_div_assoc]

/-- A nonzero reference projection is DERIVED from the actual origin IVP
on the stated small interval. No nonzero determinant or projection is assumed. -/
theorem origin_kummer_reference_integral_lower_bound {mu theta R B : ℝ}
    (K : OriginKummerPair mu theta R) (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 ≤ B) (hBR : B ≤ R)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmall : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    B ^ 2 / 4 ≤ ‖originKummerReferenceIntegral K B‖ := by
  have hErr := origin_kummer_reference_integral_error_bound K D G hD hG
    hB hBR hcoeff hbound
  have hSmallErr : ((D + 1) * G + 1 / 4) * B ^ 4 / 4 ≤ B ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_right hsmall (sq_nonneg B)
    nlinarith [sq_nonneg B]
  have hApprox := hErr.trans hSmallErr
  have ht := norm_sub_le (originKummerReferenceIntegral K B)
    (originKummerReferenceIntegral K B - ((B ^ 2 / 2 : ℝ) : ℂ))
  rw [sub_sub_cancel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ B ^ 2 / 2)] at ht
  linarith

end HBL.Profile.Kummer
