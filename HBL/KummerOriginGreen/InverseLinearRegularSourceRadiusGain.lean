import HBL.KummerOriginBasis.RegularDerivativeBound
import HBL.KummerOriginGreen.InverseLinearSourceRegularizedNoRadiusLoss
import Mathlib.Tactic

/-!
# The original regular Kummer Wronskian source has one extra factor r

The previous O(M) bound for BOTH normalized inverse-linear original
Green densities was sufficient for the weighted C1 source response,
but NOT for a uniform physical radial Hdot1 bound as the left interface
r0=L/a approaches the origin.

The original regular physical Kummer mode X(r)=x(r)/r is uniformly
bounded as r->0. Its Wronskian source density therefore satisfies
  |X(r)*F(r)/W_K(r)| <= J*M*r
when |F(r)| <= M/r and J is the genuine regular-IVP bound.
The singular density, by contrast, is only O(G*M).

The additional factor r must be retained INSIDE the original first
Cramer coefficient integral, not discarded before integration. This
is the next sharp source ingredient needed to improve r²*u' to a
true physical radial-energy estimate without a false a^-1 loss.
Neither Type-II rate nor independent generated-source order is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Profile.Kummer

theorem originGreen_inverse_linear_regular_density_one_extra_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B M : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hB : B ≤ scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ) (r : ℝ) (hr : r ∈ Ioc 0 B)
    (hF : ‖F r‖ ≤ M / r) :
    ‖originGreenSourceA K F r‖ ≤
      (1 + (D + 1) * G * B ^ 2) * M * r := by
  let J : ℝ := 1 + (D + 1) * G * B ^ 2
  have hr0 : 0 < r := hr.1
  have hscale : r ∈ Icc 0 scale := ⟨hr0.le, hr.2.trans hB⟩
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hX : ‖originPhysicalValue K.x r‖ ≤ J := by
    simpa only [J] using
      (origin_kummer_regular_physical_bound K D G hD hG
        hB hcoeff hbound r hr).1
  have hWr :
      originGreenWronskian K r =
        (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) :=
    origin_physical_wronskian_exact K hscale hr0.ne'
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
  unfold originGreenSourceA
  rw [div_eq_mul_inv, norm_mul, norm_mul, hInv]
  calc
    ‖originPhysicalValue K.x r‖ * ‖F r‖ * r ^ 2 =
        (‖originPhysicalValue K.x r‖ * (‖F r‖ * r)) * r := by ring
    _ ≤ (J * M) * r := by
      apply mul_le_mul_of_nonneg_right _ hr0.le
      exact mul_le_mul hX hFM
        (mul_nonneg (norm_nonneg _) hr0.le) hJ
    _ = (1 + (D + 1) * G * B ^ 2) * M * r := rfl

end HBL.Profile.Kummer
