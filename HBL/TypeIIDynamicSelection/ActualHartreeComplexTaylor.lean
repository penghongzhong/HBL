import HBL.TypeIIDynamicSelection.ActualHartreeComplexCubicLipschitz

/-!
Exact real-linear Taylor expansion at an arbitrary complex background.
The quartic density and cubic multiplier are those of the original
inverse-square Hartree nonlinearity. The remainder bounds retain the
perturbation amplitude to second order.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

def actualHartreeComplexRealPair (u h : ℂ) : ℝ :=
  u.re * h.re + u.im * h.im

def actualHartreeComplexDensityLinear (u h : ℂ) : ℝ :=
  4 * ‖u‖ ^ 2 * actualHartreeComplexRealPair u h

def actualHartreeComplexDensityRemainder (u h : ℂ) : ℝ :=
  2 * ‖u‖ ^ 2 * ‖h‖ ^ 2 +
    (2 * actualHartreeComplexRealPair u h + ‖h‖ ^ 2) ^ 2

def actualHartreeComplexCubicLinear (u h : ℂ) : ℂ :=
  (‖u‖ ^ 2 : ℝ) * h +
    (2 * actualHartreeComplexRealPair u h : ℝ) * u

def actualHartreeComplexCubicRemainder (u h : ℂ) : ℂ :=
  (2 * actualHartreeComplexRealPair u h : ℝ) * h +
    (‖h‖ ^ 2 : ℝ) * (u + h)

theorem actual_Hartree_complex_real_pair_bound (u h : ℂ) :
    |actualHartreeComplexRealPair u h| ≤ ‖u‖ * ‖h‖ := by
  have hs : (actualHartreeComplexRealPair u h) ^ 2 ≤
      (‖u‖ * ‖h‖) ^ 2 := by
    simp only [actualHartreeComplexRealPair, mul_pow,
      Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [sq_nonneg (u.re * h.im - u.im * h.re)]
  have hs' : |actualHartreeComplexRealPair u h| ^ 2 ≤
      (‖u‖ * ‖h‖) ^ 2 := by simpa only [sq_abs] using hs
  nlinarith only [hs', abs_nonneg (actualHartreeComplexRealPair u h),
    mul_nonneg (norm_nonneg u) (norm_nonneg h)]

theorem actual_Hartree_complex_Taylor_polynomial_identity (u h : ℂ) :
    ‖u + h‖ ^ 4 = ‖u‖ ^ 4 +
      actualHartreeComplexDensityLinear u h +
      actualHartreeComplexDensityRemainder u h ∧
    actualHartreeComplexCubic (u + h) =
      actualHartreeComplexCubic u +
      actualHartreeComplexCubicLinear u h +
      actualHartreeComplexCubicRemainder u h := by
  have hs : ‖u + h‖ ^ 2 = ‖u‖ ^ 2 +
      2 * actualHartreeComplexRealPair u h + ‖h‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, actualHartreeComplexRealPair]
    ring
  constructor
  · rw [show ‖u + h‖ ^ 4 = (‖u + h‖ ^ 2) ^ 2 by ring, hs]
    unfold actualHartreeComplexDensityLinear actualHartreeComplexDensityRemainder
    ring
  · unfold actualHartreeComplexCubic actualHartreeComplexCubicLinear
      actualHartreeComplexCubicRemainder
    rw [hs]
    push_cast
    ring

/-- All bounds follow from the actual complex polynomial; the background
need not be real and the perturbation need not belong to unweighted L2. -/
theorem actual_Hartree_complex_Taylor_polynomial_bounds
    (u h : ℂ) {A e : ℝ} (hA : 0 ≤ A) (he : 0 ≤ e)
    (hu : ‖u‖ ≤ A) (hh : ‖h‖ ≤ e) :
    |actualHartreeComplexDensityLinear u h| ≤ 4 * A ^ 3 * e ∧
    |actualHartreeComplexDensityRemainder u h| ≤
      6 * A ^ 2 * e ^ 2 + 4 * A * e ^ 3 + e ^ 4 ∧
    ‖actualHartreeComplexCubic u‖ ≤ A ^ 3 ∧
    ‖actualHartreeComplexCubicLinear u h‖ ≤ 3 * A ^ 2 * e ∧
    ‖actualHartreeComplexCubicRemainder u h‖ ≤ (3 * A + e) * e ^ 2 := by
  have hp : |actualHartreeComplexRealPair u h| ≤ A * e :=
    (actual_Hartree_complex_real_pair_bound u h).trans
      (mul_le_mul hu hh (norm_nonneg h) hA)
  have hu2 : ‖u‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
  have hh2 : ‖h‖ ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ (norm_nonneg h) hh 2
  have hadd : ‖u + h‖ ≤ A + e :=
    (norm_add_le u h).trans (add_le_add hu hh)
  have hden1 : |actualHartreeComplexDensityLinear u h| ≤ 4 * A ^ 3 * e := by
    unfold actualHartreeComplexDensityLinear
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_nonneg (sq_nonneg ‖u‖)]
    calc
      _ ≤ (4 * A ^ 2) * (A * e) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hu2 (by norm_num)) hp
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hsum : |2 * actualHartreeComplexRealPair u h + ‖h‖ ^ 2| ≤
      2 * A * e + e ^ 2 := by
    have ht := abs_add_le (2 * actualHartreeComplexRealPair u h) (‖h‖ ^ 2)
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sq_nonneg ‖h‖)] at ht
    nlinarith only [ht, hp, hh2]
  have hsquare : (2 * actualHartreeComplexRealPair u h + ‖h‖ ^ 2) ^ 2 ≤
      (2 * A * e + e ^ 2) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hsum 2
  have hdenR : |actualHartreeComplexDensityRemainder u h| ≤
      6 * A ^ 2 * e ^ 2 + 4 * A * e ^ 3 + e ^ 4 := by
    unfold actualHartreeComplexDensityRemainder
    rw [abs_of_nonneg (by positivity)]
    have hprod := mul_le_mul hu2 hh2 (sq_nonneg ‖h‖) (sq_nonneg A)
    nlinarith only [hprod, hsquare]
  have hc0 : ‖actualHartreeComplexCubic u‖ ≤ A ^ 3 := by
    unfold actualHartreeComplexCubic
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖u‖)]
    calc
      ‖u‖ ^ 2 * ‖u‖ = ‖u‖ ^ 3 := by ring
      _ ≤ A ^ 3 := pow_le_pow_left₀ (norm_nonneg u) hu 3
  have hc1 : ‖actualHartreeComplexCubicLinear u h‖ ≤ 3 * A ^ 2 * e := by
    have ht := norm_add_le (((‖u‖ ^ 2 : ℝ) : ℂ) * h)
      (((2 * actualHartreeComplexRealPair u h : ℝ) : ℂ) * u)
    have hb1 : ‖(((‖u‖ ^ 2 : ℝ) : ℂ) * h)‖ ≤ A ^ 2 * e := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖u‖)]
      exact mul_le_mul hu2 hh (norm_nonneg h) (sq_nonneg A)
    have hb2 : ‖(((2 * actualHartreeComplexRealPair u h : ℝ) : ℂ) * u)‖ ≤
        2 * A ^ 2 * e := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ ≤ (2 * (A * e)) * A :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hu
            (norm_nonneg u) (by positivity)
        _ = _ := by ring
    unfold actualHartreeComplexCubicLinear
    linarith only [ht, hb1, hb2]
  have hcR : ‖actualHartreeComplexCubicRemainder u h‖ ≤
      (3 * A + e) * e ^ 2 := by
    have ht := norm_add_le (((2 * actualHartreeComplexRealPair u h : ℝ) : ℂ) * h)
      (((‖h‖ ^ 2 : ℝ) : ℂ) * (u + h))
    have hb1 : ‖(((2 * actualHartreeComplexRealPair u h : ℝ) : ℂ) * h)‖ ≤
        2 * A * e ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ ≤ (2 * (A * e)) * e :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hh
            (norm_nonneg h) (by positivity)
        _ = _ := by ring
    have hb2 : ‖(((‖h‖ ^ 2 : ℝ) : ℂ) * (u + h))‖ ≤ e ^ 2 * (A + e) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖h‖)]
      exact mul_le_mul hh2 hadd (norm_nonneg _) (sq_nonneg e)
    unfold actualHartreeComplexCubicRemainder
    nlinarith only [ht, hb1, hb2]
  exact ⟨hden1, hdenR, hc0, hc1, hcR⟩

end HBL.TypeIIDynamicSelection
