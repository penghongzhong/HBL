import HBL.TypeIIDynamicSelection.ActualHartreeSingularGreenTimeRatioNoLeftLoss
import Mathlib.Tactic

/-!
# Common original Wronskian bound for both moving-time Green densities

The exact three-dimensional Wronskian cancels the physical 1/r
factor of either original normalized regularized Kummer solution.
Both source time derivatives can therefore be handled on the same
moving annular interval with a common coefficient G*B, not a hidden
negative power of the shrinking left interface. The Kummer regularized
mode bounds, not a full moving PDE time estimate, are explicit inputs.
-/

noncomputable section
set_option autoImplicit false
open Set
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Regular Green time density: the same no-left-radius cancellation. -/
theorem actual_Hartree_original_regular_Green_density_ratio_no_left_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (G B r : ℝ)
    (hG : 0 ≤ G) (hr : 0 < r)
    (hrB : r ≤ B) (hBR : B ≤ scale)
    (hY : ‖K.y r‖ ≤ G) :
    ‖originPhysicalValue K.y r / originGreenWronskian K r‖ ≤ G * B := by
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
      ‖originPhysicalValue K.y r / originGreenWronskian K r‖ =
        (‖K.y r‖ / r) * r ^ 2 := by
    calc
      _ = ‖originPhysicalValue K.y r‖ *
          ‖(originGreenWronskian K r)⁻¹‖ := by
            rw [div_eq_mul_inv, norm_mul]
      _ = (‖K.y r‖ / r) * r ^ 2 := by
            rw [hInv]
            simp only [originPhysicalValue, norm_div, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hr]
  rw [hNorm]
  calc
    (‖K.y r‖ / r) * r ^ 2 = ‖K.y r‖ * r := by
      field_simp [hr.ne']
    _ ≤ G * r := mul_le_mul_of_nonneg_right hY hr.le
    _ ≤ G * B := mul_le_mul_of_nonneg_left hrB hG



/-- Both ORIGINAL physical Kummer Wronskian densities on the SAME radius
admit a left-radius-uniform multiplier bound; the singular homogeneous
solution Y itself is NOT being claimed uniformly bounded. -/
theorem actual_Hartree_original_both_Green_density_ratios_no_left_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (G B r : ℝ)
    (hG : 0 ≤ G) (hr : 0 < r) (hrB : r ≤ B) (hBR : B ≤ scale)
    (hX : ‖K.x r‖ ≤ G) (hY : ‖K.y r‖ ≤ G) :
    ‖originPhysicalValue K.x r / originGreenWronskian K r‖ ≤ G * B ∧
    ‖originPhysicalValue K.y r / originGreenWronskian K r‖ ≤ G * B := by
  exact ⟨actual_Hartree_original_singular_Green_density_ratio_no_left_radius
    K G B r hG hr hrB hBR hX,
    actual_Hartree_original_regular_Green_density_ratio_no_left_radius
    K G B r hG hr hrB hBR hY⟩

end HBL.TypeIIDynamicSelection
