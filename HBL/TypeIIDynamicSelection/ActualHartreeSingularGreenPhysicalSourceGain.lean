import HBL.TypeIIDynamicSelection.ActualHartreeKummerRegularTailGain
import HBL.TypeIIDynamicSelection.ActualOriginGreenIntegrable
import HBL.KummerOriginBasis.RegularDerivativeBound
import Mathlib.Tactic

/-!
# True Hartree Green source moment times singular origin fundamental solution

The rough origin bound |X(r)| <= G/r causes an artificial positive factor
of the moving scale a when multiplied by the singular Green mode Y(r).
This file instead uses the GENUINE regular-origin Frobenius bound
|X(r)| <= 1+(D+1)*G*R² (no 1/r) and exact Wronskian inverse |W⁻¹|=r².

For the original full 3D inverse-square quartic Hartree core-radiation
source |S(y)| <= M*(1+y)^(-19/8), the integrand of the outgoing
source moment is bounded by Creg*M throughout the normalized annulus
ar>=L>=1, *independently of a*. Hence the local Green moment is
O((r-L/a)M) and its PRODUCT with the true singular basis Y(r)
is bounded by G*Creg*M, also with no factor of a or 1/(L/a).

This is a quantitative, source-faithful positive-gain component of
revised §2.13. It is not the complete actual time-dependent Hartree PDE
residual or the fixed s^(-9/4) parametrix.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

private theorem actual_hartree_rpow_shape_unit_bound
    (q : ℝ) (hq : 1 ≤ q) :
    q ^ 2 * (1 + q) ^ (-(19 / 8 : ℝ)) ≤ 1 := by
  have hqpos : 0 < q := by linarith
  have hPow :
      (1 + q) ^ (-(19 / 8 : ℝ)) ≤ q ^ (-(19 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hqpos (by linarith) (by norm_num)
  have hExponent :
      q ^ (-(19 / 8 : ℝ)) ≤ q ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hq (by norm_num)
  have hCancelR :
      q ^ (2 : ℝ) * q ^ (-(2 : ℝ)) = 1 := by
    simpa only [add_neg_cancel, Real.rpow_zero] using
      (Real.rpow_add hqpos (2 : ℝ) (-(2 : ℝ))).symm
  have hCast : q ^ (2 : ℝ) = q ^ (2 : ℕ) := by
    norm_num [Real.rpow_natCast]
  have hCancel : q ^ 2 * q ^ (-(2 : ℝ)) = 1 := by
    rw [hCast] at hCancelR
    exact hCancelR
  calc
    _ ≤ q ^ 2 * q ^ (-(2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hPow.trans hExponent) (sq_nonneg q)
    _ = 1 := hCancel

/-- The near-inner Green source moment is O(normalized interval length),
and the full singular-mode physical product has no positive power of
moving scale a or its inverse. All forcing and basis inputs are genuine. -/
theorem actual_Hartree_singular_Green_local_moment_full_product_gain
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G L R a B A ell c : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hL : 1 ≤ L) (ha : 0 < a)
    (_hOrder : L / a ≤ R) (hRscale : R < scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ t : ℝ, 0 < t → ‖z t‖ ≤ B)
    (hStrauss : ∀ t : ℝ, 1 ≤ t → t * ‖z t‖ ≤ A)
    (r : ℝ) (hr : r ∈ Icc (L / a) R) :
    let F : ℝ → ℂ :=
      fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
    let M := actualHartreePhysicalWeightedSourceConstant B A *
      ell ^ (1 / 8 : ℝ)
    let Creg := 1 + (D + 1) * G * R ^ 2
    (‖originGreenCoeffA K r F (L / a)‖ ≤
      Creg * M * (r - L / a)) ∧
    (‖originPhysicalValue K.y r *
      originGreenCoeffA K r F (L / a)‖ ≤ G * Creg * M) := by
  dsimp only
  let F : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let M : ℝ :=
    actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)
  let Creg : ℝ := 1 + (D + 1) * G * R ^ 2
  let r0 : ℝ := L / a
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hr0 : 0 < r0 := div_pos hLp ha
  have hrpos : 0 < r := hr0.trans_le hr.1
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA)
      (Real.rpow_nonneg hell.le _)
  have hCreg : 0 ≤ Creg := by dsimp [Creg]; positivity
  have hConst : 0 ≤ Creg * M := mul_nonneg hCreg hM
  have hDens (x : ℝ) (hx : x ∈ Icc r0 r) :
      ‖originGreenSourceA K F x‖ ≤ Creg * M := by
    have hxpos : 0 < x := hr0.trans_le hx.1
    have hax : 0 < a * x := mul_pos ha hxpos
    have haxL : L ≤ a * x := by
      have hh := (div_le_iff₀ ha).1 hx.1
      simpa only [r0, mul_comm] using hh
    have haxOne : 1 ≤ a * x := hL.trans haxL
    have hPhysical :=
      actual_Hartree_physical_source_unweighted_pointwise
        B A ell c (a * x) hB hA hell hellOne hc hax
        z hz hSup hStrauss
    have hF :
        ‖F x‖ ≤ a ^ 2 * M * (1 + a * x) ^ (-(19 / 8 : ℝ)) := by
      dsimp [F, M]
      rw [norm_neg, actualHartreeLaplacianScaledKummerSource, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hPhysical (sq_nonneg a)
    have hXreg :=
      (origin_kummer_regular_physical_bound
        K D G hD hG hRscale.le hcoeff hbound
        x ⟨hxpos, hx.2.trans hr.2⟩).1
    have hX : ‖originPhysicalValue K.x x‖ ≤ Creg := by
      simpa only [Creg] using hXreg
    have hWr :
        originGreenWronskian K x =
          (x : ℂ)⁻¹ ^ 2 *
            Complex.exp (-Complex.I * (x : ℂ) ^ 2 / 4) :=
      origin_physical_wronskian_exact K
        ⟨hxpos.le, (hx.2.trans hr.2).trans hRscale.le⟩ hxpos.ne'
    have hExp : ‖Complex.exp (-Complex.I * (x : ℂ) ^ 2 / 4)‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, Complex.mul_im, pow_two]
    have hWinv : ‖(originGreenWronskian K x)⁻¹‖ = x ^ 2 := by
      rw [hWr, norm_inv, norm_mul, norm_pow, norm_inv, hExp, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
      simp
    rw [originGreenSourceA, div_eq_mul_inv, norm_mul, norm_mul, hWinv]
    calc
      _ ≤ Creg *
          (a ^ 2 * M * (1 + a * x) ^ (-(19 / 8 : ℝ))) * x ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hX hF (norm_nonneg _) hCreg)
          (sq_nonneg x)
      _ = Creg * M *
          ((a * x) ^ 2 * (1 + a * x) ^ (-(19 / 8 : ℝ))) := by ring
      _ ≤ Creg * M * 1 :=
        mul_le_mul_of_nonneg_left
          (actual_hartree_rpow_shape_unit_bound (a * x) haxOne) hConst
      _ = Creg * M := by ring
  have hMoment :
      ‖originGreenCoeffA K r F r0‖ ≤
        Creg * M * (r - r0) := by
    unfold originGreenCoeffA
    have hInterval :
        ‖∫ x in r0..r, originGreenSourceA K F x‖ ≤
          ∫ _x in r0..r, Creg * M := by
      apply intervalIntegral.norm_integral_le_of_norm_le hr.1
      · filter_upwards with x hx
        exact hDens x ⟨hx.1.le, hx.2⟩
      · exact intervalIntegrable_const
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      using hInterval
  have hY : ‖originPhysicalValue K.y r‖ ≤ G / r := by
    have hBr := hbound r
      ⟨hrpos.le, hr.2.trans hRscale.le⟩
    rw [originPhysicalValue, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrpos]
    exact div_le_div_of_nonneg_right hBr.1 hrpos.le
  have hFrac : (r - r0) / r ≤ 1 :=
    (div_le_iff₀ hrpos).2 (by linarith [hr.1])
  have hGConst : 0 ≤ G * (Creg * M) :=
    mul_nonneg hG hConst
  refine ⟨?_, ?_⟩
  · simpa only [r0] using hMoment
  · calc
      ‖originPhysicalValue K.y r *
          originGreenCoeffA K r F r0‖ =
        ‖originPhysicalValue K.y r‖ * ‖originGreenCoeffA K r F r0‖ :=
        norm_mul _ _
      _ ≤ (G / r) * (Creg * M * (r - r0)) :=
        mul_le_mul hY hMoment (norm_nonneg _)
          (div_nonneg hG hrpos.le)
      _ = G * (Creg * M) * ((r - r0) / r) := by
        field_simp [hrpos.ne']
      _ ≤ G * (Creg * M) * 1 :=
        mul_le_mul_of_nonneg_left hFrac hGConst
      _ = G * Creg * M := by ring

end HBL.TypeIIDynamicSelection
