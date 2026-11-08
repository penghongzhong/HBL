import HBL.TypeIIDynamicSelection.ActualHartreeKummerRegularTailGain
import HBL.TypeIIDynamicSelection.ActualOriginGreenIntegrable
import Mathlib.Tactic

/-!
# Actual outgoing Green source moment vanishes at the moving inner boundary

The original physical Hartree source is not an abstract annular atom.
Its true spatial bound is |S(y)| <= M*(1+y)^(-19/8). Combining the
origin-normalized regular basis and the exact Wronskian yields the
pointwise outgoing density
  |X(r)F(r)/W(r)| <= G M a (ar)^(-11/8).

On the WHOLE moving Kummer annulus ar>=L the density has a bounded
supremum; its integral over [L/a,r] therefore vanishes linearly
at r=L/a, with the exact physical distance ar-L and no extra a power.

This is the local source-moment correction in the exact compatible
singular Green transport identity, essential when the singular mode
is multiplied back. It is not yet a full nonlinear Hartree PDE
O(s^(-9/4)) residual or time-uniform physical energy theorem.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_Kummer_outgoing_local_source_moment_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (G L R a B A ell c : ℝ) (hG : 0 ≤ G)
    (hL : 1 ≤ L) (ha : 0 < a)
    (_hOrder : L / a ≤ R) (hRscale : R < scale)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ x : ℝ, 0 < x → ‖z x‖ ≤ B)
    (hStrauss : ∀ x : ℝ, 1 ≤ x → x * ‖z x‖ ≤ A)
    (r : ℝ) (hr : r ∈ Icc (L / a) R) :
    let F : ℝ → ℂ :=
      fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
    let M := actualHartreePhysicalWeightedSourceConstant B A *
      ell ^ (1 / 8 : ℝ)
    ‖originGreenCoeffA K r F (L / a)‖ ≤
      G * M * (a * r - L) * L ^ (-(11 / 8 : ℝ)) := by
  dsimp only
  let F : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let M := actualHartreePhysicalWeightedSourceConstant B A *
    ell ^ (1 / 8 : ℝ)
  let r0 : ℝ := L / a
  let Cm : ℝ := G * M * a * L ^ (-(11 / 8 : ℝ))
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hr0 : 0 < r0 := div_pos hLp ha
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA)
      (Real.rpow_nonneg hell.le _)
  have hCm : 0 ≤ Cm := by dsimp [Cm]; positivity
  have hFI : IntervalIntegrable F volume r0 r :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable
      B A ell c a r0 r hB hA hell hellOne hc ha hr0
      (by simpa only [r0] using hr.1)
      z hz hSup hStrauss).neg
  have hK := origin_kummer_annulus_bound K r0 r G hr0
    (hr.2.trans_lt hRscale) hG hbound
  have hIntegrable := (actual_origin_Green_source_integrability
    K hK (by simpa only [r0] using hr.1) F hFI).1
  have hDensity (x : ℝ) (hx : x ∈ Icc r0 r) :
      ‖originGreenSourceA K F x‖ ≤ Cm := by
    have hxpos : 0 < x := hr0.trans_le hx.1
    have hax : 0 < a * x := mul_pos ha hxpos
    have haxL : L ≤ a * x := by
      have hh := (div_le_iff₀ ha).1 hx.1
      simpa only [r0, mul_comm] using hh
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
    have hBasis := hbound x ⟨hxpos.le, hx.2.trans (hr.2.trans_lt hRscale).le⟩
    have hX : ‖originPhysicalValue K.x x‖ ≤ G / x := by
      rw [originPhysicalValue, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hxpos]
      exact div_le_div_of_nonneg_right hBasis.2.2.1 hxpos.le
    have hW :
        originGreenWronskian K x =
          (x : ℂ)⁻¹ ^ 2 *
            Complex.exp (-Complex.I * (x : ℂ) ^ 2 / 4) :=
      origin_physical_wronskian_exact K
        ⟨hxpos.le, hx.2.trans (hr.2.trans_lt hRscale).le⟩ hxpos.ne'
    have hE : ‖Complex.exp (-Complex.I * (x : ℂ) ^ 2 / 4)‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, Complex.mul_im, pow_two]
    have hInv : ‖(originGreenWronskian K x)⁻¹‖ = x ^ 2 := by
      rw [hW, norm_inv, norm_mul, norm_pow, norm_inv, hE, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
      simp
    have hTail :
        (a * x) * (1 + a * x) ^ (-(19 / 8 : ℝ)) ≤
          (a * x) ^ (-(11 / 8 : ℝ)) := by
      have hp :
          (1 + a * x) ^ (-(19 / 8 : ℝ)) ≤
            (a * x) ^ (-(19 / 8 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hax (by linarith) (by norm_num)
      calc
        _ ≤ (a * x) * (a * x) ^ (-(19 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_left hp hax.le
        _ = (a * x) ^ (1 : ℝ) * (a * x) ^ (-(19 / 8 : ℝ)) := by
          rw [Real.rpow_one]
        _ = (a * x) ^ ((1 : ℝ) + (-(19 / 8 : ℝ))) :=
          (Real.rpow_add hax (1 : ℝ) (-(19 / 8 : ℝ))).symm
        _ = (a * x) ^ (-(11 / 8 : ℝ)) := by
          congr 1
          norm_num
    have hPower :
        (a * x) ^ (-(11 / 8 : ℝ)) ≤ L ^ (-(11 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hLp haxL (by norm_num)
    rw [originGreenSourceA, div_eq_mul_inv, norm_mul, norm_mul, hInv]
    calc
      _ ≤ (G / x) *
        (a ^ 2 * M * (1 + a * x) ^ (-(19 / 8 : ℝ))) * x ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hX hF (norm_nonneg _) (by positivity)) (sq_nonneg x)
      _ = G * M * a * ((a * x) *
          (1 + a * x) ^ (-(19 / 8 : ℝ))) := by
        field_simp [hxpos.ne']
      _ ≤ G * M * a * (a * x) ^ (-(11 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hTail (by positivity)
      _ ≤ Cm :=
        mul_le_mul_of_nonneg_left hPower (by positivity)
  have hNorm :
      ‖originGreenCoeffA K r F r0‖ ≤ Cm * (r - r0) := by
    unfold originGreenCoeffA
    have hInterval :
        ‖∫ x in r0..r, originGreenSourceA K F x‖ ≤
          ∫ _x in r0..r, Cm := by
      apply intervalIntegral.norm_integral_le_of_norm_le
        (by simpa only [r0] using hr.1)
      · filter_upwards with x hx
        exact hDensity x ⟨hx.1.le, hx.2⟩
      · exact intervalIntegrable_const
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      using hInterval
  calc
    ‖originGreenCoeffA K r F (L / a)‖ ≤
        Cm * (r - r0) := by simpa only [r0] using hNorm
    _ = G * M * (a * r - L) * L ^ (-(11 / 8 : ℝ)) := by
      dsimp [Cm, r0]
      field_simp [ha.ne']

end HBL.TypeIIDynamicSelection
