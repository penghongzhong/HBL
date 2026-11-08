import HBL.TypeIIDynamicSelection.ActualHartreeSpeedRegularGreen
import HBL.KummerOriginBasis.PhysicalWronskian
import Mathlib.Tactic

/-!
# Genuine selected speed corrections: no singular Green scaling loss

The two ACTUAL Hartree modulation directions S_b,S_omega satisfy
  ||S_b(r)||, ||S_omega(r)|| <= C_s a/r.
Their origin Green outgoing integrals must be multiplied by the singular
physical solution Y(r). Using the true normalized Wronskian and physical
basis bounds gives, on the moving annulus, the product bound
  ||Y(r) A_speed(r)|| <= G^2 C_s a (|p_b|+|p_omega|).
This has precisely the factor a needed to cancel the proven selected
speed size O((N+Q)/a). No artificial forcing packet is substituted and
no blowup rate is presupposed.

Unlike the true core-radiation source, the selected speed sources have
only a 1/r pointwise envelope; they must NOT inherit the 19/8 tail
from the baseline Hartree interaction. This theorem controls their
correct additional singular Green channel separately.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_speed_correction_singular_Green_no_scale_loss :
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
        (G L c a B : ℝ),
        0 ≤ G → 1 ≤ L → 0 < a → B ≤ 1 → B < scale →
        a * |c| ≤ 1 → L / a ≤ B →
        (∀ x ∈ Icc 0 scale,
          ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
          ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G) →
        ∀ (p : ℝ × ℝ) (r : ℝ), r ∈ Icc (L / a) B →
          let Fsp : ℝ → ℂ := fun x =>
            (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
            (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
          ‖originPhysicalValue K.y r *
            originGreenCoeffA K r Fsp (L / a)‖ ≤
            G ^ 2 * Cs * a * (|p.1| + |p.2|) := by
  obtain ⟨Cs, hCs, hSpeed⟩ :=
    actual_Hartree_scaled_speed_outer_inverse_radius
  refine ⟨Cs, hCs, ?_⟩
  intro mu theta scale K G L c a B hG hL ha hBOne hBR hSmall hOrder
    hbound p r hr
  dsimp only
  let Fsp : ℝ → ℂ := fun x =>
    (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
    (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
  let r0 : ℝ := L / a
  let P : ℝ := |p.1| + |p.2|
  let Cg : ℝ := G * Cs * a * P
  have hLp : 0 < L := by linarith
  have hr0 : 0 < r0 := div_pos hLp ha
  have hrp : 0 < r := hr0.trans_le hr.1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hSpeedEnv := hSpeed L c a B hL ha hBOne hSmall
  have hF (x : ℝ) (hx : x ∈ Icc r0 r) :
      ‖Fsp x‖ ≤ (Cs * a / x) * P := by
    have hxB : x ∈ Icc (L / a) B :=
      ⟨by simpa only [r0] using hx.1, hx.2.trans hr.2⟩
    have hh := hSpeedEnv x hxB
    have h1 :
        ‖(-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x‖ ≤
          |p.1| * (Cs * a / x) := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hh.1 (abs_nonneg _)
    have h2 :
        ‖(-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x‖ ≤
          |p.2| * (Cs * a / x) := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hh.2 (abs_nonneg _)
    calc
      ‖Fsp x‖ ≤
          ‖(-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x‖ +
          ‖(-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x‖ :=
        norm_add_le _ _
      _ ≤ |p.1| * (Cs * a / x) + |p.2| * (Cs * a / x) :=
        add_le_add h1 h2
      _ = (Cs * a / x) * P := by dsimp [P]; ring
  have hDensity (x : ℝ) (hx : x ∈ Icc r0 r) :
      ‖originGreenSourceA K Fsp x‖ ≤ Cg := by
    have hxpos : 0 < x := hr0.trans_le hx.1
    have hxb : x ≤ scale := (hx.2.trans hr.2).trans hBR.le
    have hX : ‖originPhysicalValue K.x x‖ ≤ G / x := by
      have hRef := hbound x ⟨hxpos.le,hxb⟩
      rw [originPhysicalValue, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hxpos]
      exact div_le_div_of_nonneg_right hRef.2.2.1 hxpos.le
    have hWr :
        originGreenWronskian K x =
          (x : ℂ)⁻¹ ^ 2 *
            Complex.exp (-Complex.I * (x : ℂ) ^ 2 / 4) :=
      origin_physical_wronskian_exact K ⟨hxpos.le,hxb⟩ hxpos.ne'
    have hExp : ‖Complex.exp (-Complex.I * (x : ℂ) ^ 2 / 4)‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, Complex.mul_im, pow_two]
    have hInv : ‖(originGreenWronskian K x)⁻¹‖ = x ^ 2 := by
      rw [hWr, norm_inv, norm_mul, norm_pow, norm_inv, hExp, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
      simp
    rw [originGreenSourceA, div_eq_mul_inv, norm_mul, norm_mul, hInv]
    calc
      _ ≤ (G / x) * ((Cs * a / x) * P) * x ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hX (hF x hx) (norm_nonneg _)
            (by positivity)) (sq_nonneg x)
      _ = Cg := by dsimp [Cg, P]; field_simp [hxpos.ne']
  have hMoment :
      ‖originGreenCoeffA K r Fsp r0‖ ≤ Cg * (r - r0) := by
    unfold originGreenCoeffA
    have hRaw :
        ‖∫ x in r0..r, originGreenSourceA K Fsp x‖ ≤
          Cg * |r-r0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le hr.1] at hx
      exact hDensity x ⟨hx.1.le,hx.2⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hr.1)] at hRaw
    exact hRaw
  have hY : ‖originPhysicalValue K.y r‖ ≤ G / r := by
    have hRef := hbound r ⟨hrp.le,hr.2.trans hBR.le⟩
    rw [originPhysicalValue, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrp]
    exact div_le_div_of_nonneg_right hRef.1 hrp.le
  have hRatio : (r - r0) / r ≤ 1 :=
    (div_le_iff₀ hrp).2 (by linarith [hr.1])
  calc
    ‖originPhysicalValue K.y r * originGreenCoeffA K r Fsp r0‖ =
        ‖originPhysicalValue K.y r‖ *
          ‖originGreenCoeffA K r Fsp r0‖ := norm_mul _ _
    _ ≤ (G / r) * (Cg * (r-r0)) :=
      mul_le_mul hY hMoment (norm_nonneg _)
        (div_nonneg hG hrp.le)
    _ = (G * Cg) * ((r-r0) / r) := by
      field_simp [hrp.ne']
    _ ≤ (G * Cg) * 1 :=
      mul_le_mul_of_nonneg_left hRatio (mul_nonneg hG hCg)
    _ = G ^ 2 * Cs * a * (|p.1| + |p.2|) := by
      dsimp [Cg, P]
      ring

end HBL.TypeIIDynamicSelection
