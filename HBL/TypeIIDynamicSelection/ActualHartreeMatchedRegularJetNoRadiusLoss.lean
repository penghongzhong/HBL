import HBL.TypeIIDynamicSelection.ActualHartreeMatchedKummerInteriorSourceBound
import HBL.KummerOriginBasis.PhysicalWronskian
import Mathlib.Tactic

/-!
# Original Hartree Cramer regular coefficient: exact radius cancellation

The original physical Kummer Wronskian is r^{-2} exp(-i r²/4).
The singular fundamental mode y(r)/r and its derivative have factors
r^{-1} and r^{-2}, but their Cramer numerator is multiplied by
the inverse Wronskian of absolute value r². Keeping this cancellation
BEFORE estimating norms gives an upper bound for the regular coefficient
that is independent of inverse powers of the moving left radius.

The left data U, DU are the original Fredholm Cauchy coordinates, not
a new independently chosen upper-boundary amplitude. The theorem is
pointwise in the genuine Kummer pair; its future physical application
must construct U,DU from the actual source-selected Fredholm orbit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The *original* Cramer coefficient has no inverse moving-radius loss.
The y/a and dy/a-y/a² factors cancel exactly against W(a)^{-1}. -/
theorem actual_Hartree_matched_regular_coefficient_no_left_radius_loss
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b G : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hG : 0 ≤ G)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G)
    (F : ℝ → ℂ) (U DU : ℂ) :
    ‖actualOriginMatchedRegularCoeff K a b F U DU‖ ≤
      G * (a * ‖DU‖ + (a + 1) * ‖U‖) := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hnorma : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hmode := hbound a ⟨ha.le, hab.trans hb⟩
  have hW :
      originGreenWronskian K a =
        (a : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (a : ℂ) ^ 2 / 4) :=
    origin_physical_wronskian_exact K ⟨ha.le, hab.trans hb⟩ ha.ne'
  have hExp : ‖Complex.exp (-Complex.I * (a : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have hInv : ‖(originGreenWronskian K a)⁻¹‖ = a ^ 2 := by
    rw [hW, norm_inv, norm_mul, norm_pow, norm_inv, hExp, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    simp
  let N : ℂ :=
    originPhysicalValue K.y a * DU -
      originPhysicalSlope K.y K.dy a * U
  have hNumerator :
      N * (a : ℂ) ^ 2 =
        (a : ℂ) * K.y a * DU -
          ((a : ℂ) * K.dy a - K.y a) * U := by
    dsimp [N]
    unfold originPhysicalValue originPhysicalSlope
    field_simp [haC]
  have hCoefficient :
      ‖actualOriginMatchedRegularCoeff K a b F U DU‖ =
        ‖N‖ * a ^ 2 := by
    rw [actual_origin_matched_Kummer_regular_coefficient]
    change ‖N / originGreenWronskian K a‖ = _
    rw [div_eq_mul_inv, norm_mul, hInv]
  have hFirst :
      ‖(a : ℂ) * K.y a * DU‖ ≤ (a * G) * ‖DU‖ := by
    simp only [norm_mul, hnorma]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmode.1 ha.le) (norm_nonneg DU)
  have hMiddle :
      ‖(a : ℂ) * K.dy a - K.y a‖ ≤ a * G + G := by
    calc
      _ ≤ ‖(a : ℂ) * K.dy a‖ + ‖K.y a‖ := norm_sub_le _ _
      _ = a * ‖K.dy a‖ + ‖K.y a‖ := by
        rw [norm_mul, hnorma]
      _ ≤ a * G + G :=
        add_le_add (mul_le_mul_of_nonneg_left hmode.2 ha.le) hmode.1
  have hSecond :
      ‖((a : ℂ) * K.dy a - K.y a) * U‖ ≤
        (a * G + G) * ‖U‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hMiddle (norm_nonneg U)
  calc
    ‖actualOriginMatchedRegularCoeff K a b F U DU‖ =
        ‖N‖ * a ^ 2 := hCoefficient
    _ = ‖(a : ℂ) * K.y a * DU -
        ((a : ℂ) * K.dy a - K.y a) * U‖ := by
          rw [← hNumerator, norm_mul, norm_pow, hnorma]
    _ ≤ ‖(a : ℂ) * K.y a * DU‖ +
        ‖((a : ℂ) * K.dy a - K.y a) * U‖ := norm_sub_le _ _
    _ ≤ (a * G) * ‖DU‖ + (a * G + G) * ‖U‖ :=
      add_le_add hFirst hSecond
    _ = G * (a * ‖DU‖ + (a + 1) * ‖U‖) := by ring

/-- The ORIGINAL regular homogeneous Cramer part has a uniformly bounded
r-weighted profile, using only the global regularized origin IVP modes. -/
theorem actual_Hartree_matched_regular_part_weighted_no_radius_loss
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b G : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hG : 0 ≤ G)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ) (U DU : ℂ) (r : ℝ) (hr : r ∈ Icc a b) :
    ‖(r : ℂ) *
        (actualOriginMatchedRegularCoeff K a b F U DU *
          originPhysicalValue K.x r)‖ ≤
      G ^ 2 * (a * ‖DU‖ + (a + 1) * ‖U‖) := by
  have hr0 : 0 < r := ha.trans_le hr.1
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hCoeff :=
    actual_Hartree_matched_regular_coefficient_no_left_radius_loss
      K a b G ha hab hb hG
      (fun x hx => ⟨(hbound x hx).1,(hbound x hx).2.1⟩) F U DU
  have hx : ‖K.x r‖ ≤ G := (hbound r ⟨hr0.le,hr.2.trans hb⟩).2.2
  have hEq :
      (r : ℂ) *
        (actualOriginMatchedRegularCoeff K a b F U DU *
          originPhysicalValue K.x r) =
        actualOriginMatchedRegularCoeff K a b F U DU * K.x r := by
    unfold originPhysicalValue
    field_simp [hrC]
  rw [hEq, norm_mul]
  calc
    ‖actualOriginMatchedRegularCoeff K a b F U DU‖ * ‖K.x r‖ ≤
        (G * (a * ‖DU‖ + (a + 1) * ‖U‖)) * G :=
      mul_le_mul hCoeff hx (norm_nonneg _) (by positivity)
    _ = G ^ 2 * (a * ‖DU‖ + (a + 1) * ‖U‖) := by ring

end HBL.TypeIIDynamicSelection
