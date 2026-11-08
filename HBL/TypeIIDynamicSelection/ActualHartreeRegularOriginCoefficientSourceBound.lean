import HBL.TypeIIDynamicSelection.ActualHartreeCanonicalJetBound
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer
import HBL.KummerOriginBasis.PhysicalWronskian
import Mathlib.Tactic

/-!
# Genuine regular Kummer homogeneous amplitude from the Fredholm source

In the original origin-normalized radial Kummer gauge, the unique
regular coefficient of the physically forced Green field is
gamma = (Y(r0) DU - Y'(r0) U) / W(r0).
The actual singular physical basis has O(1/r0) value and O(1/r0²)
slope; the exact Wronskian inverse is O(r0²). Therefore gamma is
bounded with NO negative power of the moving inner radius.

The second theorem substitutes the genuine two-channel Fredholm
weighted source norm for the left Cauchy jet. This closes the true
regular homogeneous branch coefficient interface of revised §2.13,
not the full time-dependent Hartree PDE remainder O(s^(-9/4)).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

theorem actual_Hartree_Kummer_regular_coefficient_no_inverse_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (G R r : ℝ) (hG : 0 ≤ G) (hR : R ≤ 1)
    (hRScale : R ≤ scale)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hr : r ∈ Ioc 0 R) (F : ℝ → ℂ) (U DU : ℂ) :
    ‖actualOriginMatchedRegularCoeff K r R F U DU‖ ≤
      2 * G * (‖U‖ + r * ‖DU‖) := by
  have hrpos : 0 < r := hr.1
  have hrOne : r ≤ 1 := hr.2.trans hR
  have hK := hbound r ⟨hrpos.le, hr.2.trans hRScale⟩
  have hY : ‖originPhysicalValue K.y r‖ ≤ G / r := by
    rw [originPhysicalValue, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrpos]
    exact div_le_div_of_nonneg_right hK.1 hrpos.le
  have hYdot :
      ‖originPhysicalSlope K.y K.dy r‖ ≤ G / r + G / r ^ 2 := by
    unfold originPhysicalSlope
    calc
      _ ≤ ‖K.dy r / (r : ℂ)‖ +
          ‖K.y r / (r : ℂ) ^ 2‖ := norm_sub_le _ _
      _ = ‖K.dy r‖ / r + ‖K.y r‖ / r ^ 2 := by
        simp only [norm_div, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hrpos]
      _ ≤ G / r + G / r ^ 2 :=
        add_le_add
          (div_le_div_of_nonneg_right hK.2.1 hrpos.le)
          (div_le_div_of_nonneg_right hK.1 (sq_nonneg r))
  have hWr :
      originGreenWronskian K r =
        (r : ℂ)⁻¹ ^ 2 *
          Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) :=
    origin_physical_wronskian_exact K
      ⟨hrpos.le, hr.2.trans hRScale⟩ hrpos.ne'
  have hExp : ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have hWinv : ‖(originGreenWronskian K r)⁻¹‖ = r ^ 2 := by
    rw [hWr, norm_inv, norm_mul, norm_pow, norm_inv, hExp, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    simp
  have hNumerator :
      ‖originPhysicalValue K.y r * DU -
        originPhysicalSlope K.y K.dy r * U‖ ≤
        (G / r) * ‖DU‖ + (G / r + G / r ^ 2) * ‖U‖ := by
    calc
      _ ≤ ‖originPhysicalValue K.y r * DU‖ +
          ‖originPhysicalSlope K.y K.dy r * U‖ := norm_sub_le _ _
      _ = ‖originPhysicalValue K.y r‖ * ‖DU‖ +
          ‖originPhysicalSlope K.y K.dy r‖ * ‖U‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ (G / r) * ‖DU‖ +
          (G / r + G / r ^ 2) * ‖U‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_right hY (norm_nonneg DU))
          (mul_le_mul_of_nonneg_right hYdot (norm_nonneg U))
  have hGr : G * (r + 1) ≤ 2 * G := by
    nlinarith [mul_nonneg hG (sub_nonneg.mpr hrOne)]
  have hTwo : G * r * ‖DU‖ ≤ 2 * G * r * ‖DU‖ := by
    have hPos : 0 ≤ G * r * ‖DU‖ := by positivity
    nlinarith
  rw [actual_origin_matched_Kummer_regular_coefficient, div_eq_mul_inv,
    norm_mul, hWinv]
  calc
    _ ≤ ((G / r) * ‖DU‖ +
        (G / r + G / r ^ 2) * ‖U‖) * r ^ 2 :=
      mul_le_mul_of_nonneg_right hNumerator (sq_nonneg r)
    _ = G * r * ‖DU‖ + G * (r + 1) * ‖U‖ := by
      field_simp [hrpos.ne']
      ring
    _ ≤ G * r * ‖DU‖ + 2 * G * ‖U‖ :=
      add_le_add_left
        (mul_le_mul_of_nonneg_right hGr (norm_nonneg U)) _
    _ ≤ 2 * G * r * ‖DU‖ + 2 * G * ‖U‖ :=
      add_le_add_right hTwo _
    _ = 2 * G * (‖U‖ + r * ‖DU‖) := by ring

theorem actual_Hartree_Fredholm_regular_coefficient_from_weighted_source
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (G R L a : ℝ) (hG : 0 ≤ G)
    (hR : R ≤ 1) (hRScale : R ≤ scale)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hL : 2 < L) (ha : 0 < a) (hLR : L / a ≤ R)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (hcp : Continuous Fp) (hcm : Continuous Fm)
    (F : ℝ → ℂ) :
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    let N := innerWeightedNorm (7 / 4 : ℝ) Fp +
      innerWeightedNorm (7 / 4 : ℝ) Fm
    let Cf := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
    ‖actualOriginMatchedRegularCoeff K (L / a) R F J.1 J.2‖ ≤
      (2 * G) * (Cf * N) := by
  dsimp only
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let N := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let Cf := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
  have hLp : 0 < L := by linarith
  have hrpos : 0 < L / a := div_pos hLp ha
  have hJ :=
    actual_Hartree_canonical_inner_jet_source_norm_bound
      Fp Fm hp hm hcp hcm L a hL ha
  have hK :=
    actual_Hartree_Kummer_regular_coefficient_no_inverse_radius
      K G R (L / a) hG hR hRScale hbound ⟨hrpos,hLR⟩
      F J.1 J.2
  have hGpos : 0 ≤ 2 * G := by positivity
  calc
    ‖actualOriginMatchedRegularCoeff K (L / a) R F J.1 J.2‖ ≤
      2 * G * (‖J.1‖ + (L / a) * ‖J.2‖) := hK
    _ ≤ 2 * G * (Cf * N) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [J, Cf, N] using hJ) hGpos

end HBL.TypeIIDynamicSelection
