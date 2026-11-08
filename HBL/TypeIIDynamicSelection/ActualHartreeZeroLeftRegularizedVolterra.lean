import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer
import HBL.KummerOriginGreen.InverseLinearSourceRegularizedNoRadiusLoss
import Mathlib.Tactic

/-!
# Genuine zero-left-jet Kummer Volterra bound with no moving-radius singular loss

The original Cramer matched solution with zero left value AND slope
contains a singular coefficient -A(a). This is NOT an independent
homogeneous amplitude: it exactly cancels the outgoing primitive A(a).
Multiplication by the physical radius r exposes the bounded regularized
IVP pair y,x, not the singular physical basis y/r,x/r.

An inverse-linear source |F(s)|<=M/s has BOTH original Green densities
bounded by G M (strictly verified separately). Their genuine coefficient
primitives then yield a uniform weighted bound
  |r w(r)| <= 2 G² (b-a) M
with no inverse a. This is the correct Volterra estimate for repeated
small spectral corrections preserving the original left Fredholm C¹ jet.

Only the actual origin Kummer pair, its finite positive annular validity,
and bounded regularized IVP modes are used. The conclusion is *not*
a global nonlinear Hartree residual or dynamical blowup law.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_zero_left_Kummer_regularized_Volterra_identity
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) (r : ℝ) (hr : r ∈ Icc a b) :
    (r : ℂ) * actualOriginMatchedKummerValue K a b F 0 0 r =
      K.y r * (originGreenCoeffA K b F r - originGreenCoeffA K b F a) +
        K.x r * originGreenCoeffB K a F r := by
  have hr0 : 0 < r := ha.trans_le hr.1
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hSing :
      actualOriginMatchedSingularCoeff K a b F 0 0 =
        -originGreenCoeffA K b F a := by
    rw [actual_origin_matched_Kummer_singular_eq_obstruction K hK hab F 0 0]
    unfold actualMomentLockedIntervalObstruction actualOriginOutgoingTrace
    simp
  have hReg : actualOriginMatchedRegularCoeff K a b F 0 0 = 0 := by
    rw [actual_origin_matched_Kummer_regular_coefficient K a b F 0 0]
    simp
  unfold actualOriginMatchedKummerValue originGreenValue
  rw [hSing, hReg]
  simp only [zero_mul, add_zero]
  unfold originPhysicalValue
  field_simp [hrC]; ring

theorem actual_Hartree_zero_left_Kummer_regularized_Volterra_value_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G M : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ scale) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C)
    (hbound : ∀ x ∈ Icc 0 scale,
        ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M / x)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖(r : ℂ) * actualOriginMatchedKummerValue K a b F 0 0 r‖ ≤
      2 * G ^ 2 * (b - a) * M := by
  have hr0 : 0 < r := ha.trans_le hr.1
  have hModes := hbound r ⟨hr0.le, hr.2.trans hb⟩
  have hCoeffs (x : ℝ) (hx : x ∈ Icc a b) :=
    originGreen_inverse_linear_coefficients_regularized_uniform
      K a b G M ha hab hb hG hM hbound F hF x hx
  have hAr := (hCoeffs r hr).1
  have hAa := (hCoeffs a ⟨le_refl a, hab⟩).1
  have hBr := (hCoeffs r hr).2
  have hId :=
    actual_Hartree_zero_left_Kummer_regularized_Volterra_identity
      K a b C ha hab hK F r hr
  rw [hId]
  calc
    ‖K.y r * (originGreenCoeffA K b F r - originGreenCoeffA K b F a) +
        K.x r * originGreenCoeffB K a F r‖ ≤
      ‖K.y r‖ * (‖originGreenCoeffA K b F r‖ +
        ‖originGreenCoeffA K b F a‖) +
      ‖K.x r‖ * ‖originGreenCoeffB K a F r‖ := by
      calc
        _ ≤ ‖K.y r * (originGreenCoeffA K b F r -
                originGreenCoeffA K b F a)‖ +
              ‖K.x r * originGreenCoeffB K a F r‖ :=
            norm_add_le _ _
        _ = ‖K.y r‖ * ‖originGreenCoeffA K b F r -
              originGreenCoeffA K b F a‖ +
            ‖K.x r‖ * ‖originGreenCoeffB K a F r‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ ‖K.y r‖ * (‖originGreenCoeffA K b F r‖ +
                ‖originGreenCoeffA K b F a‖) +
              ‖K.x r‖ * ‖originGreenCoeffB K a F r‖ :=
            add_le_add_right
              (mul_le_mul_of_nonneg_left
                (norm_sub_le _ _) (norm_nonneg _)) _
    _ ≤ G * ((G * M) * (b - r) + (G * M) * (b - a)) +
        G * ((G * M) * (r - a)) := by
      apply add_le_add
      · exact mul_le_mul hModes.1 (add_le_add hAr hAa)
          (add_nonneg (norm_nonneg _) (norm_nonneg _)) hG
      · exact mul_le_mul hModes.2 hBr (norm_nonneg _) hG
    _ = 2 * G ^ 2 * (b - a) * M := by ring

end HBL.TypeIIDynamicSelection
