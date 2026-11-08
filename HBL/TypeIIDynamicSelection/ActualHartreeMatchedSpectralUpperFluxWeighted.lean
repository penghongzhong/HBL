import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralLeftC1Exact
import HBL.KummerOriginBasis.RegularDerivativeBound
import Mathlib.Tactic

/-!
# True matched Hartree spectral upper flux: uniform REGULAR basis, no inverse left radius

The origin-normalized singular Kummer mode behaves like 1/r; hence its
unweighted moving-annulus supremum is not uniform as a=L/scale -> 0.
The upper OUTGOING obstruction, however, only uses the regular physical
mode x(r)/r. That mode has an O(1) bound independent of the left endpoint.

For the matched spectral correction q=d w0, the exact original Wronskian
satisfies |W(r)^(-1)|=r², cancelling the true weighted q-source r^-2.
The resulting outgoing coefficient is bounded using ONLY the original
regular physical Kummer mode and source moment, not a global bound on the
singular fundamental solution.

A genuine weighted estimate for the matched w0 must still be produced
from the same nonlinear Hartree orbit; the present module isolates and
verifies the correct radius-uniform flux mapping.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Original regular-source Wronskian cancellation, using a bound
for the regular physical Kummer value (never the singular mode). -/
theorem actual_Hartree_regular_outgoing_source_from_weighted_profile
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G b : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hb : b ≤ scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧
        ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (q : ℝ → ℂ) (H : ℝ) (hH : 0 ≤ H)
    (r : ℝ) (hr : r ∈ Ioc 0 b)
    (hsource : ‖q r‖ ≤ H / r ^ 2) :
    ‖originGreenSourceA K q r‖ ≤
      (1 + (D + 1) * G * b ^ 2) * H := by
  let J : ℝ := 1 + (D + 1) * G * b ^ 2
  have hr0 : 0 < r := hr.1
  have hrscale : r ∈ Icc 0 scale := ⟨hr0.le, hr.2.trans hb⟩
  have hReg := (origin_kummer_regular_physical_bound
      K D G hD hG hb hcoeff hbound r hr).1
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hWr :
      originGreenWronskian K r =
        (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) := by
    exact origin_physical_wronskian_exact K hrscale hr0.ne'
  have hExp : ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have hInv : ‖(originGreenWronskian K r)⁻¹‖ = r ^ 2 := by
    rw [hWr, norm_inv, norm_mul, norm_pow, norm_inv, hExp, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    simp
  have hQr : ‖q r‖ * r ^ 2 ≤ H := by
    calc
      ‖q r‖ * r ^ 2 ≤ (H / r ^ 2) * r ^ 2 :=
        mul_le_mul_of_nonneg_right hsource (sq_nonneg _)
      _ = H := by field_simp [hr0.ne']
  unfold originGreenSourceA
  rw [div_eq_mul_inv, norm_mul, norm_mul, hInv]
  calc
    ‖originPhysicalValue K.x r‖ * ‖q r‖ * r ^ 2 =
        ‖originPhysicalValue K.x r‖ * (‖q r‖ * r ^ 2) := by ring
    _ ≤ J * H :=
      mul_le_mul hReg hQr
        (mul_nonneg (norm_nonneg _) (sq_nonneg _)) hJ
    _ = (1 + (D + 1) * G * b ^ 2) * H := rfl

/-- The ORIGINAL spectral correction source has a quantitatively controlled
outgoing obstruction without any a^(-1) or a^(-2). The only norm assumption
is the explicit original physical weighted field bound H; the regular
Kummer factor is uniform as the left interface tends to the origin. -/
theorem actual_Hartree_matched_spectral_upper_obstruction_weighted_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G a b H : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hH : 0 ≤ H)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧
        ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (F : ℝ → ℂ) (U DU d : ℂ)
    (hProfile : ∀ r ∈ Icc a b,
      ‖actualOriginMatchedKummerValue K a b F U DU r‖ ≤ H / r ^ 2) :
    ‖actualMomentLockedIntervalObstruction K a b
        (actualHartreeMatchedSpectralFirstSource K a b F U DU d) 0 0‖ ≤
      (1 + (D + 1) * G * b ^ 2) * (‖d‖ * H) * (b - a) := by
  let q : ℝ → ℂ := actualHartreeMatchedSpectralFirstSource K a b F U DU d
  let M : ℝ := ‖d‖ * H
  have hM : 0 ≤ M := mul_nonneg (norm_nonneg d) hH
  have hDensity : ∀ r ∈ Icc a b,
      ‖originGreenSourceA K q r‖ ≤
        (1 + (D + 1) * G * b ^ 2) * M := by
    intro r hr
    have hr0 : 0 < r := ha.trans_le hr.1
    have hBase := hProfile r hr
    have hQ : ‖q r‖ ≤ M / r ^ 2 := by
      change ‖d * actualOriginMatchedKummerValue K a b F U DU r‖ ≤ _
      rw [norm_mul]
      have h := mul_le_mul_of_nonneg_left hBase (norm_nonneg d)
      dsimp [M]
      convert h using 1 <;> ring
    exact actual_Hartree_regular_outgoing_source_from_weighted_profile
      K D G b hD hG hb hcoeff hbound q M hM r ⟨hr0, hr.2⟩ hQ
  have hCoeff :
      ‖originGreenCoeffA K b q a‖ ≤
        ((1 + (D + 1) * G * b ^ 2) * M) * (b-a) := by
    have hInt :
        ‖originGreenCoeffA K b q a‖ ≤
          ((1 + (D + 1) * G * b ^ 2) * M) * |b-a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro r hr
      rw [uIoc_of_le hab] at hr
      exact hDensity r ⟨hr.1.le, hr.2⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hInt
  have hIdent :
      actualMomentLockedIntervalObstruction K a b q 0 0 =
        -originGreenCoeffA K b q a := by
    unfold actualMomentLockedIntervalObstruction actualOriginOutgoingTrace
    simp
  rw [hIdent, norm_neg]
  simpa only [q, M] using hCoeff

/-- When the first matched problem has its REAL original outgoing
compatibility canceled, the corresponding correction changes its upper
flux by at most an O(|d|) weighted-source moment. The left C¹ trace
continues to match the Fredholm jet exactly (previous theorem). -/
theorem actual_Hartree_matched_spectral_corrected_upper_flux_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G a b H : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hH : 0 ≤ H)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧
        ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r)
    (U DU d : ℂ)
    (hCompatible : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (hProfile : ∀ r ∈ Icc a b,
      ‖actualOriginMatchedKummerValue K a b F U DU r‖ ≤ H / r ^ 2) :
    ‖actualOriginOutgoingTrace K b
        (actualHartreeMatchedSpectralCorrectedValue K a b F U DU d b)
        (deriv (actualHartreeMatchedSpectralCorrectedValue
          K a b F U DU d) b)‖ ≤
      (1 + (D + 1) * G * b ^ 2) * (‖d‖ * H) * (b - a) := by
  have hFlux := actual_Hartree_matched_spectral_upper_defect_exact
    K a b ha hab hb F hF U DU d hCompatible
  dsimp only at hFlux
  rw [hFlux, norm_neg]
  exact actual_Hartree_matched_spectral_upper_obstruction_weighted_bound
    K D G a b H hD hG ha hab hb.le hH hcoeff hbound F U DU d hProfile

end HBL.TypeIIDynamicSelection
