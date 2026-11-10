import HBL.KummerOriginBasis.AsymptoticBound
import HBL.KummerOriginGreen.GreenBridge
import Mathlib.Tactic

/-!
# A true extra r² from the ORIGINAL regular Frobenius Kummer mode

The original singular Green source density is X(r) F(r)/W(r),
where X(r)=K.x(r)/r and 1/|W(r)|=r². Unlike a coarse norm
of the singular homogeneous physical solution Y, the genuine
regular mode obeys X(r)=1+O(r²) from the original Frobenius
initial-value construction. Hence |X(r)/W(r)|=O(r²), gaining
one more small-radius factor than the earlier G*r estimate.

The coefficient bound follows from the ORIGINAL ODE (not a
postulated source envelope, scaling rate or PDE remainder).
The dynamical time-derivative magnitude of the true Hartree
source and its four-region feedback remain independent
open obligations.
-/

noncomputable section
set_option autoImplicit false
open Set
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Exact Frobenius gain of two positive powers at the original
moving matching radius: no inverse radius and no arbitrary
singular Green basis budget. -/
theorem actual_Hartree_original_singular_Green_density_Frobenius_quadratic_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B r : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hr : 0 < r) (hrB : r ≤ B) (hBR : B ≤ scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
      ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G) :
    ‖originPhysicalValue K.x r / originGreenWronskian K r‖ ≤
      (1 + (D + 1) * G * B ^ 2) * r ^ 2 := by
  have hR : r ∈ Ioc 0 scale := ⟨hr, hrB.trans hBR⟩
  have hAsym :
      ‖originPhysicalValue K.x r - 1‖ ≤ (D + 1) * G * r ^ 2 :=
    (origin_kummer_asymptotic_bound K D G hD hG hcoeff hbound r hR).2
  have hXNorm :
      ‖originPhysicalValue K.x r‖ ≤ 1 + (D + 1) * G * B ^ 2 := by
    have hNorm : ‖originPhysicalValue K.x r‖ ≤
        ‖originPhysicalValue K.x r - 1‖ + 1 := by
      have hEq : originPhysicalValue K.x r =
          (originPhysicalValue K.x r - 1) + 1 := by ring
      calc
        _ = ‖(originPhysicalValue K.x r - 1) + 1‖ := congrArg norm hEq
        _ ≤ ‖originPhysicalValue K.x r - 1‖ + 1 := by
          simpa only [norm_one] using
            (norm_add_le (originPhysicalValue K.x r - 1) (1 : ℂ))
    have h2 : r ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg (B-r)]
    have hDG : 0 ≤ (D + 1) * G :=
      mul_nonneg (by linarith) hG
    calc
      _ ≤ ‖originPhysicalValue K.x r - 1‖ + 1 := hNorm
      _ ≤ (D + 1) * G * r ^ 2 + 1 := by
        linarith only [hAsym]
      _ ≤ 1 + (D + 1) * G * B ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left h2 hDG]
  have hW :
      originGreenWronskian K r =
        (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) :=
    origin_physical_wronskian_exact K
      ⟨hr.le, hrB.trans hBR⟩ hr.ne'
  have hExp : ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have hInv : ‖(originGreenWronskian K r)⁻¹‖ = r ^ 2 := by
    rw [hW, norm_inv, norm_mul, norm_pow, norm_inv, hExp, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    simp
  calc
    ‖originPhysicalValue K.x r / originGreenWronskian K r‖ =
        ‖originPhysicalValue K.x r‖ * r ^ 2 := by
      rw [div_eq_mul_inv, norm_mul, hInv]
    _ ≤ (1 + (D + 1) * G * B ^ 2) * r ^ 2 :=
      mul_le_mul_of_nonneg_right hXNorm (sq_nonneg r)

end HBL.TypeIIDynamicSelection
