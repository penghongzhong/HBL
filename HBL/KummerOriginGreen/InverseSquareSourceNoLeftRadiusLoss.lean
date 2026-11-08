import HBL.KummerOriginGreen.UniformBound
import Mathlib.Tactic

/-!
# Exact original Wronskian cancellation for an inverse-square Hartree source

The physical original quartic Hartree source has the ACTUAL radial bound
  ||F(r)|| <= Q/r²,  a <= r <= b.
The origin-normalized Kummer Wronskian satisfies
  ||W_K(r)^(-1)|| = r², not merely an arbitrary annular constant.
Thus both actual Green densities have ||Y F/W||, ||X F/W|| <= C Q
and BOTH original Wronskian Green coefficients and the full value/slope
have bounds with NO a^(-2) factor:
  ||G[F](r)||+||dG[F](r)|| <= 2*C²*(b-a)*Q.

This is a meaningful PHYSICAL source-class gain over the old
uniform-sup source bound Q/a². It will be used to strengthen the genuine
Hartree Cramer selected first spectral correction. No blowup rate,
positive time order or whole four-region PDE estimate is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Profile.Kummer

theorem originGreen_inverse_square_source_no_left_radius_loss
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    {a b C Q : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (_hQ : 0 ≤ Q)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) {r : ℝ} (hr : r ∈ Icc a b)
    (hF : ‖F r‖ ≤ Q / r ^ 2) :
    ‖originGreenSourceA K F r‖ ≤ C * Q ∧
      ‖originGreenSourceB K F r‖ ≤ C * Q := by
  have hrpos : 0 < r := ha.trans_le hr.1
  rcases hK r hr with ⟨_, _, _, _, _, _, hy, _, hx, _, _⟩
  have hw :=
    originGreenWronskian_exact K hK hr
  have hExp :
      ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have hInv :
      ‖(originGreenWronskian K r)⁻¹‖ = r ^ 2 := by
    rw [hw, norm_inv, norm_mul, norm_pow, norm_inv,
      hExp, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrpos]
    simp
  have hQratio : ‖F r‖ * r ^ 2 ≤ Q := by
    calc
      ‖F r‖ * r ^ 2 ≤ Q / r ^ 2 * r ^ 2 :=
        mul_le_mul_of_nonneg_right hF (sq_nonneg r)
      _ = Q := by field_simp [hrpos.ne']
  have hBound (p : ℂ) (hp : ‖p‖ ≤ C) :
      ‖p * F r / originGreenWronskian K r‖ ≤ C * Q := by
    rw [div_eq_mul_inv, norm_mul, norm_mul, hInv]
    calc
      ‖p‖ * ‖F r‖ * r ^ 2 =
          ‖p‖ * (‖F r‖ * r ^ 2) := by ring
      _ ≤ C * Q :=
        mul_le_mul hp hQratio
          (mul_nonneg (norm_nonneg _) (sq_nonneg _)) hC
  exact ⟨hBound _ hx, hBound _ hy⟩

/-- The true 1/r² original-source decay cancels the 1/W(r) gain
BEFORE taking the Green integral. Hence no inverse left radius appears
in either original regular or singular Green coefficient estimate. -/
theorem originGreen_inverse_square_coefficients_no_left_radius_loss
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C Q : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ Q / x ^ 2)
    {r : ℝ} (hr : r ∈ Icc a b) :
    ‖originGreenCoeffA K b F r‖ ≤ (C * Q) * (b - r) ∧
    ‖originGreenCoeffB K a F r‖ ≤ (C * Q) * (r - a) := by
  have hA : ‖originGreenCoeffA K b F r‖ ≤
      (C * Q) * |b - r| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hr.2] at hx
    have hxr : x ∈ Icc a b := ⟨hr.1.trans hx.1.le, hx.2⟩
    exact (originGreen_inverse_square_source_no_left_radius_loss
      K ha hC hQ hK F hxr (hF x hxr)).1
  have hB : ‖originGreenCoeffB K a F r‖ ≤
      (C * Q) * |r - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hr.1] at hx
    have hxr : x ∈ Icc a b := ⟨hx.1.le, hx.2.trans hr.2⟩
    exact (originGreen_inverse_square_source_no_left_radius_loss
      K ha hC hQ hK F hxr (hF x hxr)).2
  simpa only [abs_of_nonneg (sub_nonneg.mpr hr.2),
    abs_of_nonneg (sub_nonneg.mpr hr.1)] using And.intro hA hB

/-- NO r0^(-2) loss: the actual original Green field and its spatial
derivative are controlled by the true inverse-square source envelope Q. -/
theorem originGreen_inverse_square_value_slope_no_left_radius_loss
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C Q : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ Q / x ^ 2)
    {r : ℝ} (hr : r ∈ Icc a b) :
    ‖originGreenValue K a b F r‖ +
      ‖originGreenSlope K a b F r‖ ≤
      (2 * C ^ 2 * (b - a)) * Q := by
  have hcoef :=
    originGreen_inverse_square_coefficients_no_left_radius_loss
      K a b C Q ha hC hQ hK F hF hr
  rcases hK r hr with ⟨_, _, _, _, _, _, hy, hdy, hx, hdx, _⟩
  have hCQ : 0 ≤ C * Q := mul_nonneg hC hQ
  have hBound (p q : ℂ) (hp : ‖p‖ ≤ C) (hq : ‖q‖ ≤ C) :
      ‖p * originGreenCoeffA K b F r +
        q * originGreenCoeffB K a F r‖ ≤
        C ^ 2 * (b - a) * Q := by
    calc
      _ ≤ ‖p‖ * ‖originGreenCoeffA K b F r‖ +
          ‖q‖ * ‖originGreenCoeffB K a F r‖ := by
        simpa only [norm_mul] using norm_add_le
          (p * originGreenCoeffA K b F r)
          (q * originGreenCoeffB K a F r)
      _ ≤ C * ((C * Q) * (b - r)) +
          C * ((C * Q) * (r - a)) :=
        add_le_add
          (mul_le_mul hp hcoef.1 (norm_nonneg _) hC)
          (mul_le_mul hq hcoef.2 (norm_nonneg _) hC)
      _ = C ^ 2 * (b - a) * Q := by ring
  have hVal := hBound (originPhysicalValue K.y r)
    (originPhysicalValue K.x r) hy hx
  have hSlope := hBound (originPhysicalSlope K.y K.dy r)
    (originPhysicalSlope K.x K.dx r) hdy hdx
  change ‖originPhysicalValue K.y r * originGreenCoeffA K b F r +
      originPhysicalValue K.x r * originGreenCoeffB K a F r‖ +
    ‖originPhysicalSlope K.y K.dy r * originGreenCoeffA K b F r +
      originPhysicalSlope K.x K.dx r * originGreenCoeffB K a F r‖ ≤ _
  calc
    _ ≤ C ^ 2 * (b - a) * Q + C ^ 2 * (b - a) * Q :=
      add_le_add hVal hSlope
    _ = (2 * C ^ 2 * (b - a)) * Q := by ring

end HBL.Profile.Kummer
