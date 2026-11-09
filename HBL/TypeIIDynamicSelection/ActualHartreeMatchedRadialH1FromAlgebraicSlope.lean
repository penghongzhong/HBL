import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer
import Mathlib.Tactic

/-!
# Genuine almost-everywhere radial Hdot1 energy from the original Kummer slope

The native matched Green integrability certificate already proves that
the algebraic source-dependent Cramer slope is the true derivative of
the matched Kummer field almost everywhere on the actual positive
matching interval. No pointwise continuity of the original Hartree
radiation or its nonlocal source is needed.

The right input to the radial-energy integral is a uniform bound on
r*|Slope(r)|. It is NOT a bound on unweighted |Slope|, which would
generally introduce an artificial inverse shrinking radius.

This independent bridge introduces no Hartree source envelope:
a source-specific theorem must produce the slope bound from the one
actual quartic Riesz forcing and its unique real Cramer modulation.
It is not a nonlinear time-order estimate or a prescribed blowup rate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Exact finite-interval 3D radial gradient integral for an actual
compatible origin-Kummer Green solution. The only numerical input is
the *algebraic* radius-weighted slope bound, whose derivative
identification is obtained from the existing native a.e. certificate. -/
theorem actual_Hartree_matched_radial_H1_of_algebraic_slope_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C E : ℝ) (hab : a ≤ b) (_hE : 0 ≤ E)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) (hFI : IntervalIntegrable F volume a b)
    (U DU : ℂ)
    (hCompat : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (hPoint : ∀ r ∈ Icc a b,
      ‖(r : ℂ) * actualOriginMatchedKummerSlope
        K a b F U DU r‖ ≤ E) :
    let W := actualOriginMatchedKummerValue K a b F U DU
    (∫ r in Icc a b, r ^ 2 * ‖deriv W r‖ ^ 2) ≤
      (b - a) * E ^ 2 := by
  dsimp only
  let W := actualOriginMatchedKummerValue K a b F U DU
  let g : ℝ → ℝ := fun r => r ^ 2 * ‖deriv W r‖ ^ 2
  have hCertificate :
      ActualOriginMatchedKummerCertificate K a b F U DU :=
    (actual_origin_matched_Kummer_certificate_iff
      K hK hab F hFI U DU).2 hCompat
  have hDerivativeAE :
      ∀ᵐ r : ℝ ∂volume, r ∈ Icc a b →
        HasDerivAt W
          (actualOriginMatchedKummerSlope K a b F U DU r) r := by
    filter_upwards [hCertificate.2.2.2.2.2] with r hr hrmem
    simpa only [W] using (hr hrmem).1
  have hEnergyBound (r : ℝ) (hr : r ∈ Icc a b)
      (hDeriv : HasDerivAt W
        (actualOriginMatchedKummerSlope K a b F U DU r) r) :
      g r ≤ E ^ 2 := by
    have hP := hPoint r hr
    have hNormR : ‖(r : ℂ)‖ = |r| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, hNormR] at hP
    have hNonneg : 0 ≤ |r| *
        ‖actualOriginMatchedKummerSlope K a b F U DU r‖ :=
      mul_nonneg (abs_nonneg _) (norm_nonneg _)
    calc
      g r =
          (|r| * ‖actualOriginMatchedKummerSlope
            K a b F U DU r‖) ^ 2 := by
        dsimp [g]
        rw [hDeriv.deriv]
        nlinarith [sq_abs r]
      _ ≤ E ^ 2 := pow_le_pow_left₀ hNonneg hP 2
  have hFinite : (volume : Measure ℝ) (Icc a b) < ⊤ := by
    simp only [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hAE : ∀ᵐ r : ℝ ∂volume, r ∈ Icc a b →
      ‖g r‖ ≤ E ^ 2 := by
    filter_upwards [hDerivativeAE] with r hr hrmem
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [g]; positivity)]
    exact hEnergyBound r hrmem (hr hrmem)
  have hNorm := norm_setIntegral_le_of_norm_le_const_ae'
    (μ := volume) (s := Icc a b) (f := g) (C := E ^ 2)
    hFinite hAE
  have hIntegral :
      ‖∫ r in Icc a b, g r‖ ≤ E ^ 2 * (b - a) := by
    simpa only [Real.volume_real_Icc_of_le hab] using hNorm
  calc
    (∫ r in Icc a b, r ^ 2 * ‖deriv W r‖ ^ 2) =
        ∫ r in Icc a b, g r := rfl
    _ ≤ ‖∫ r in Icc a b, g r‖ :=
      (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm
    _ ≤ E ^ 2 * (b - a) := hIntegral
    _ = (b - a) * E ^ 2 := by ring

end HBL.TypeIIDynamicSelection
