import HBL.KummerOriginGreen.GreenBridge
import HBL.KummerOriginBasis.PhysicalWronskian
import Mathlib.Tactic

/-!
# Original outgoing singular Green time density: no shrinking-left-radius loss

The original normalized Kummer regular numerator is x(r)/r, whereas
the original exact three-dimensional physical Wronskian has inverse norm
r^2. Their product is therefore r * ‖x(r)‖, not a large inverse
power of the left matching radius r0=L/a.

This is the actual spatial multiplier in the moving-time mean-value
estimate of the original singular Green coefficient A, not an
assumed fixed-annulus norm of the full singular mode y(r)/r.

A bound on the ORIGINAL normalized regular mode x on [0,scale]
is still required. The theorem assumes no time rate, synthetic
source, independent selected speed, or PDE residual.
-/

noncomputable section
set_option autoImplicit false

open Set
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- No hidden factor 1/r0: on any positive original Kummer radius r
the exact X/W multiplier equals r times the true bounded regular mode.
The upper bound G * B is uniform as the lower endpoint tends to zero. -/
theorem actual_Hartree_original_singular_Green_density_ratio_no_left_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (G B r : ℝ)
    (hG : 0 ≤ G) (hr : 0 < r)
    (hrB : r ≤ B) (hBR : B ≤ scale)
    (hX : ‖K.x r‖ ≤ G) :
    ‖originPhysicalValue K.x r / originGreenWronskian K r‖ ≤ G * B := by
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
  have hNorm :
      ‖originPhysicalValue K.x r / originGreenWronskian K r‖ =
        (‖K.x r‖ / r) * r ^ 2 := by
    calc
      _ = ‖originPhysicalValue K.x r‖ *
          ‖(originGreenWronskian K r)⁻¹‖ := by
            rw [div_eq_mul_inv, norm_mul]
      _ = (‖K.x r‖ / r) * r ^ 2 := by
            rw [hInv]
            simp only [originPhysicalValue, norm_div, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hr]
  rw [hNorm]
  calc
    (‖K.x r‖ / r) * r ^ 2 = ‖K.x r‖ * r := by
      field_simp [hr.ne']
    _ ≤ G * r := mul_le_mul_of_nonneg_right hX hr.le
    _ ≤ G * B := mul_le_mul_of_nonneg_left hrB hG

end HBL.TypeIIDynamicSelection
