import HBL.TypeIIDynamicSelection.ActualHartreeFixedKummerBasisMovingSpectrum
import Mathlib.Tactic

/-!
# Original Kummer Green moments: radius-weighted spectral defect without hidden basis loss

The exact origin normalization is X(r) = x(r)/r and Y(r) = y(r)/r.
Multiplying the *whole* original Green field by r before using the triangle
inequality eliminates the apparent singular factor in both fundamental modes.
The resulting bound uses the actual source integrals, not an assumed profile
envelope or a shrinking-annulus OriginBasisOn constant.

The last theorem substitutes the genuine time-dependent adjusted quartic
Hartree source (with its explicit modulation terms). It does not infer a
positive time exponent from a coefficient integral, nor assert that the
modulation functions form a constructed PDE orbit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Literal two-original-moment weighted Green estimate. Unlike the
fixed-annulus C^3 bound, its right side has no hidden OriginBasisOn
constant and no inverse left matching radius. -/
theorem actual_Hartree_origin_Green_weighted_exact_moments
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a B G : ℝ) (ha : 0 < a) (_hab : a ≤ B) (hB : B ≤ scale)
    (hbound : ∀ x ∈ Icc 0 scale, ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ) (r : ℝ) (hr : r ∈ Icc a B) :
    ‖(r : ℂ) * originGreenValue K a B F r‖ ≤
      G * (‖originGreenCoeffA K B F r‖ +
        ‖originGreenCoeffB K a F r‖) := by
  have hrpos : 0 < r := ha.trans_le hr.1
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hrScale : r ∈ Icc 0 scale := ⟨hrpos.le, hr.2.trans hB⟩
  have hy : ‖K.y r‖ ≤ G := (hbound r hrScale).1
  have hx : ‖K.x r‖ ≤ G := (hbound r hrScale).2
  have hY : (r : ℂ) * originPhysicalValue K.y r = K.y r := by
    unfold originPhysicalValue
    field_simp [hrC]
  have hX : (r : ℂ) * originPhysicalValue K.x r = K.x r := by
    unfold originPhysicalValue
    field_simp [hrC]
  have hSplit :
      (r : ℂ) * originGreenValue K a B F r =
        K.y r * originGreenCoeffA K B F r +
        K.x r * originGreenCoeffB K a F r := by
    unfold originGreenValue
    calc
      _ = ((r : ℂ) * originPhysicalValue K.y r) *
          originGreenCoeffA K B F r +
          ((r : ℂ) * originPhysicalValue K.x r) *
          originGreenCoeffB K a F r := by ring
      _ = _ := by rw [hY, hX]
  rw [hSplit]
  calc
    ‖K.y r * originGreenCoeffA K B F r +
        K.x r * originGreenCoeffB K a F r‖ ≤
      ‖K.y r‖ * ‖originGreenCoeffA K B F r‖ +
        ‖K.x r‖ * ‖originGreenCoeffB K a F r‖ := by
          simpa only [norm_mul] using
            (norm_add_le
              (K.y r * originGreenCoeffA K B F r)
              (K.x r * originGreenCoeffB K a F r))
    _ ≤ G * ‖originGreenCoeffA K B F r‖ +
        G * ‖originGreenCoeffB K a F r‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    _ = G * (‖originGreenCoeffA K B F r‖ +
        ‖originGreenCoeffB K a F r‖) := by ring

/-- The ORIGINAL evolving spectral operator evaluated on the same
normalized Green integrals; there is no assumed weighted profile bound
and no radius-dependent OriginBasisOn constant. -/
theorem actual_Hartree_fixed_basis_spectral_defect_exact_moments
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (mu theta : ℝ → ℝ) (r0 : ℝ → ℝ) (B G : ℝ)
    (hG : 0 ≤ G) (hB : B ≤ scale)
    (hbound : ∀ x ∈ Icc 0 scale, ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℝ → ℂ) (s r : ℝ)
    (hr0 : 0 < r0 s) (hr : r ∈ Icc (r0 s) B) :
    ‖(r : ℂ) * (actualHartreeFrozenBasisMovingSpectrumResidual
        K mu theta r0 B F s r - F s r)‖ ≤
      (|mu s - mu0| + |theta s - theta0|) *
        (G * (‖originGreenCoeffA K B (F s) r‖ +
          ‖originGreenCoeffB K (r0 s) (F s) r‖)) := by
  let d : ℂ :=
    frozenZeroCoeff (mu s) (theta s) - frozenZeroCoeff mu0 theta0
  have hGreen :=
    actual_Hartree_origin_Green_weighted_exact_moments
      K (r0 s) B G hr0 (hr.1.trans hr.2) hB hbound (F s) r hr
  have hd :
      ‖d‖ ≤ |mu s - mu0| + |theta s - theta0| := by
    dsimp [d]
    exact frozenZeroCoeff_difference_norm_le
      (mu s) (theta s) mu0 theta0
  have hcoef :
      0 ≤ G * (‖originGreenCoeffA K B (F s) r‖ +
        ‖originGreenCoeffB K (r0 s) (F s) r‖) := by
    exact mul_nonneg hG
      (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hEq :
      (r : ℂ) * (actualHartreeFrozenBasisMovingSpectrumResidual
          K mu theta r0 B F s r - F s r) =
        d * ((r : ℂ) * originGreenValue K (r0 s) B (F s) r) := by
    rw [actual_Hartree_fixed_basis_moving_spectrum_exact]
    dsimp [d]
    ring
  rw [hEq, norm_mul]
  calc
    ‖d‖ * ‖(r : ℂ) * originGreenValue K (r0 s) B (F s) r‖ ≤
      ‖d‖ * (G * (‖originGreenCoeffA K B (F s) r‖ +
        ‖originGreenCoeffB K (r0 s) (F s) r‖)) :=
      mul_le_mul_of_nonneg_left hGreen (norm_nonneg d)
    _ ≤ (|mu s - mu0| + |theta s - theta0|) *
        (G * (‖originGreenCoeffA K B (F s) r‖ +
          ‖originGreenCoeffB K (r0 s) (F s) r‖)) :=
      mul_le_mul_of_nonneg_right hd hcoef

/-- Specialization to the actual time-dependent Hartree Riesz source and
its explicit two modulation source terms. In particular the Green
coefficients in the conclusion are the original UNSWAPPED integrals,
not free constants or order tags. -/
theorem actual_Hartree_true_adjusted_source_spectral_exact_moments
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (mu theta a ell c : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ) (b w Z : ℝ → ℂ)
    (B G s r : ℝ) (hG : 0 ≤ G) (hB : B ≤ scale)
    (hbound : ∀ x ∈ Icc 0 scale, ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (hr0 : 0 < actualHartreeSlowInnerRadius (ell s) / a s)
    (hr : r ∈ Icc (actualHartreeSlowInnerRadius (ell s) / a s) B) :
    let F : ℝ → ℂ :=
      actualHartreeTrueMovingAdjustedSource a ell c z b w Z s
    ‖(r : ℂ) *
        (actualHartreeFrozenBasisMovingSpectrumResidual K mu theta
          (fun t => actualHartreeSlowInnerRadius (ell t) / a t) B
          (fun t => actualHartreeTrueMovingAdjustedSource a ell c z b w Z t)
          s r - F r)‖ ≤
      (|mu s - mu0| + |theta s - theta0|) *
        (G * (‖originGreenCoeffA K B F r‖ +
          ‖originGreenCoeffB K
            (actualHartreeSlowInnerRadius (ell s) / a s) F r‖)) := by
  exact actual_Hartree_fixed_basis_spectral_defect_exact_moments
    K mu theta
    (fun t => actualHartreeSlowInnerRadius (ell t) / a t)
    B G hG hB hbound
    (fun t => actualHartreeTrueMovingAdjustedSource a ell c z b w Z t)
    s r hr0 hr

end HBL.TypeIIDynamicSelection
