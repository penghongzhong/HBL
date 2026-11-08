import HBL.KummerOriginGreen.GreenBridge
import HBL.KummerOriginBasis.PhysicalWronskian
import Mathlib.Tactic

/-!
# Exact origin regularized Green densities for an inverse-LINEAR source

The origin-normalized physical fundamental modes y(r)/r, x(r)/r
are singular/regular respectively. But the regularized IVP modes y,x
are bounded on the entire compact interval [0,R].

For a source |F(r)| <= M/r, the EXACT physical Wronskian
|W_K(r)^(-1)| = r² gives
  |(x(r)/r)F(r)/W_K(r)| <= G M,
  |(y(r)/r)F(r)/W_K(r)| <= G M.
Neither density needs an OriginBasisOn bound for the singular physical
basis; only the true globally regularized IVP norms are used.

The inverse-LINEAR source class arises when the ORIGINAL matched field
has the natural weighted bound |r u(r)|<=M and the perturbation source
is the actual spectral displacement d*u(r). This is the key input
towards a zero-left-jet Volterra correction uniform in the moving
left interface.

No new PDE source-envelope hypothesis or Type-II rate is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Profile.Kummer

theorem originGreen_inverse_linear_source_regularized_uniform
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (G M : ℝ) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Icc 0 scale,
        ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ) (r : ℝ) (hr : r ∈ Ioc 0 scale)
    (hF : ‖F r‖ ≤ M / r) :
    ‖originGreenSourceA K F r‖ ≤ G * M ∧
      ‖originGreenSourceB K F r‖ ≤ G * M := by
  have hr0 : 0 < r := hr.1
  have hModes := hbound r ⟨hr0.le,hr.2⟩
  have hWr :
      originGreenWronskian K r =
        (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) := by
    exact origin_physical_wronskian_exact K ⟨hr0.le,hr.2⟩ hr0.ne'
  have hExp : ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have hInv : ‖(originGreenWronskian K r)⁻¹‖ = r ^ 2 := by
    rw [hWr, norm_inv, norm_mul, norm_pow, norm_inv, hExp, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    simp
  have hFM : ‖F r‖ * r ≤ M := by
    calc
      ‖F r‖ * r ≤ (M / r) * r :=
        mul_le_mul_of_nonneg_right hF hr0.le
      _ = M := by field_simp [hr0.ne']
  have hDensity (p : ℝ → ℂ) (hp : ‖p r‖ ≤ G) :
      ‖originPhysicalValue p r * F r / originGreenWronskian K r‖ ≤
        G * M := by
    rw [div_eq_mul_inv, norm_mul, norm_mul, hInv]
    have hVal : ‖originPhysicalValue p r‖ = ‖p r‖ / r := by
      unfold originPhysicalValue
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    rw [hVal]
    calc
      ‖p r‖ / r * ‖F r‖ * r ^ 2 =
          ‖p r‖ * (‖F r‖ * r) := by
            field_simp [hr0.ne']
            ring
      _ ≤ G * M :=
        mul_le_mul hp hFM
          (mul_nonneg (norm_nonneg _) hr0.le) hG
  exact ⟨hDensity K.x hModes.2, hDensity K.y hModes.1⟩

/-- Both genuine Wronskian coefficient primitives are controlled by
the regularized origin basis, with NO inverse-left-radius constant. -/
theorem originGreen_inverse_linear_coefficients_regularized_uniform
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b G M : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ scale) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Icc 0 scale,
        ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M / x)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖originGreenCoeffA K b F r‖ ≤ (G * M) * (b - r) ∧
      ‖originGreenCoeffB K a F r‖ ≤ (G * M) * (r - a) := by
  have hA : ‖originGreenCoeffA K b F r‖ ≤ (G * M) * |b - r| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hr.2] at hx
    have hxr : x ∈ Icc a b := ⟨hr.1.trans hx.1.le, hx.2⟩
    exact (originGreen_inverse_linear_source_regularized_uniform
      K G M hG hM hbound F x
        ⟨ha.trans_le hxr.1, hxr.2.trans hb⟩ (hF x hxr)).1
  have hB : ‖originGreenCoeffB K a F r‖ ≤ (G * M) * |r - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hr.1] at hx
    have hxr : x ∈ Icc a b := ⟨hx.1.le,hx.2.trans hr.2⟩
    exact (originGreen_inverse_linear_source_regularized_uniform
      K G M hG hM hbound F x
        ⟨ha.trans_le hxr.1, hxr.2.trans hb⟩ (hF x hxr)).2
  simpa only [abs_of_nonneg (sub_nonneg.mpr hr.2),
    abs_of_nonneg (sub_nonneg.mpr hr.1)] using And.intro hA hB

end HBL.Profile.Kummer
