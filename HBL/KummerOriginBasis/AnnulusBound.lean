import HBL.KummerOriginBasis.PhysicalWronskian
import HBL.KummerOriginBasis.CertificateDefinitions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace HBL.Profile.Kummer

/-- Explicit transfer of regularized bounds to a prescribed positive annulus. -/
theorem origin_kummer_annulus_bound {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b G : ℝ)
    (ha : 0 < a) (hb : b < R) (hG : 0 ≤ G)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G) :
    OriginBasisOn K a b (G * (1 / a + 1 / a ^ 2) + b ^ 2 + 1) := by
  intro r hr
  have hr0 : 0 < r := ha.trans_le hr.1
  have hrR : r < R := hr.2.trans_lt hb
  have hr' : r ∈ Icc 0 R := ⟨hr0.le, hrR.le⟩
  have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hy := origin_kummer_physical_jets mu theta r hr0.ne' K.y K.dy
    ((K.y_deriv r hr').hasDerivAt (Icc_mem_nhds hr0 hrR))
    ((K.dy_deriv r hr').hasDerivAt (Icc_mem_nhds hr0 hrR))
  have hx := origin_kummer_physical_jets mu theta r hr0.ne' K.x K.dx
    ((K.x_deriv r hr').hasDerivAt (Icc_mem_nhds hr0 hrR))
    ((K.dx_deriv r hr').hasDerivAt (Icc_mem_nhds hr0 hrR))
  have hW := origin_physical_wronskian_exact K hr' hr0.ne'
  have hN : ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have hi : ‖(originPhysicalValue K.y r * originPhysicalSlope K.x K.dx r -
      originPhysicalSlope K.y K.dy r * originPhysicalValue K.x r)⁻¹‖ = r ^ 2 := by
    rw [hW, norm_inv, norm_mul, norm_pow, norm_inv, hN, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    simp
  have hG₁ : 0 ≤ G * (1 / a + 1 / a ^ 2) := by positivity
  have hv (u : ℝ → ℂ) (hu : ‖u r‖ ≤ G) :
      ‖originPhysicalValue u r‖ ≤ G / a := by
    dsimp [originPhysicalValue]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact div_le_div₀ hG hu ha hr.1
  have hd (u v : ℝ → ℂ) (hu : ‖u r‖ ≤ G) (hv' : ‖v r‖ ≤ G) :
      ‖originPhysicalSlope u v r‖ ≤ G * (1 / a + 1 / a ^ 2) := by
    dsimp [originPhysicalSlope]
    calc
      _ ≤ ‖v r / (r : ℂ)‖ + ‖u r / (r : ℂ) ^ 2‖ := norm_sub_le _ _
      _ = ‖v r‖ / r + ‖u r‖ / r ^ 2 := by
        simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      _ ≤ G / a + G / a ^ 2 := by gcongr <;> exact hr.1
      _ = _ := by ring
  obtain ⟨hyb, hdyb, hxb, hdxb⟩ := hbound r hr'
  have hvalue : G / a ≤ G * (1 / a + 1 / a ^ 2) := by
    have hnon : 0 ≤ G / a ^ 2 := by positivity
    nlinarith [show G * (1 / a + 1 / a ^ 2) = G / a + G / a ^ 2 by ring]
  have hlast : r ^ 2 ≤ b ^ 2 := by nlinarith [hr.2]
  refine ⟨hy.1, hy.2, hx.1, hx.2, hW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hW]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hn)) (Complex.exp_ne_zero _)
  · exact (hv K.y hyb).trans (hvalue.trans (by nlinarith [sq_nonneg b]))
  · exact (hd K.y K.dy hyb hdyb).trans (by nlinarith [sq_nonneg b])
  · exact (hv K.x hxb).trans (hvalue.trans (by nlinarith [sq_nonneg b]))
  · exact (hd K.x K.dx hxb hdxb).trans (by nlinarith [sq_nonneg b])
  · rw [hi]
    linarith
end HBL.Profile.Kummer
