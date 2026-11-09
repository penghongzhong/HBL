import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSlopeFromTraceEnergyBound
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer
import Mathlib.Tactic

/-!
# Genuine 3D radial Hdot1 estimate for a compatible matched Kummer field

The precise source class here is interval-integrable, NOT necessarily
pointwise continuous. The existing Hartree matched Green certificate
proves the algebraically defined original Green slope equals the genuine
derivative almost everywhere. We then combine the exact Cramer
outgoing-trace radial slope estimate with the physical 3D energy weight
r² dr. The integrable square of the true a.e. derivative is controlled
with no inverse shrinking left radius, via the original finite-interval
radial-volume estimate, rather than inserting an abstract Hdot1 axiom.

As a generic lemma, the zero-left source slope E and Fredholm outgoing
trace Ct*a are visible hypotheses; the corresponding genuine Hartree
sources/unique real speed are to be supplied by the existing physical
producers in the source-specific composite. No time exponent or Type-II
rate is assumed or asserted here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Integral radial Hdot1 bound from the actual (a.e.) derivative of
the matched Green value, not merely a formal Green-slope expression. -/
theorem actual_Hartree_full_matched_radial_H1_from_original_trace
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C D G E Ct : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hE : 0 ≤ E) (hCt : 0 ≤ Ct)
    (hK : OriginBasisOn K a b C)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ)
    (hFI : IntervalIntegrable F volume a b)
    (U DU : ℂ)
    (hCompatible : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (hTrace : ‖actualOriginOutgoingTrace K a U DU‖ ≤ Ct * a)
    (hZero : ∀ r ∈ Icc a b,
      ‖(r : ℂ) * actualOriginMatchedKummerSlope
        K a b F 0 0 r‖ ≤ E) :
    let W := actualOriginMatchedKummerValue K a b F U DU
    let Efull : ℝ := E + (b + 1) * G * Ct +
      2 * (D + 1) * G ^ 2 * b ^ 2 *
        (a * ‖DU‖ + (a + 1) * ‖U‖)
    (∫ r in Icc a b, r ^ 2 * ‖deriv W r‖ ^ 2) ≤
      (b - a) * Efull ^ 2 := by
  dsimp only
  let W := actualOriginMatchedKummerValue K a b F U DU
  let Efull : ℝ := E + (b + 1) * G * Ct +
    2 * (D + 1) * G ^ 2 * b ^ 2 *
      (a * ‖DU‖ + (a + 1) * ‖U‖)
  let g : ℝ → ℝ := fun r => r ^ 2 * ‖deriv W r‖ ^ 2
  have hBzero : 0 ≤ b := (ha.trans_le hab).le
  have hEfull : 0 ≤ Efull := by
    dsimp [Efull]
    positivity
  have hCertificate :
      ActualOriginMatchedKummerCertificate K a b F U DU :=
    (actual_origin_matched_Kummer_certificate_iff
      K hK hab F hFI U DU).2 hCompatible
  have hDerivativeAE :
      ∀ᵐ r : ℝ ∂volume, r ∈ Icc a b →
        HasDerivAt W
          (actualOriginMatchedKummerSlope K a b F U DU r) r := by
    filter_upwards [hCertificate.2.2.2.2.2] with r hr hrmem
    simpa only [W] using (hr hrmem).1
  have hBound (r : ℝ) (hr : r ∈ Icc a b)
      (hDeriv : HasDerivAt W
        (actualOriginMatchedKummerSlope K a b F U DU r) r) :
      g r ≤ Efull ^ 2 := by
    have hrp : 0 < r := ha.trans_le hr.1
    have hPoint :=
      actual_Hartree_full_matched_radial_energy_from_zero_left_and_jet
        K a b C D G E Ct ha hab hb hD hG hCt
        hK hcoeff hbound F U DU hCompatible hTrace
        r hr (hZero r hr)
    have hNormR : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
    rw [norm_mul, hNormR] at hPoint
    have hNonneg : 0 ≤
        r * ‖actualOriginMatchedKummerSlope K a b F U DU r‖ :=
      mul_nonneg hrp.le (norm_nonneg _)
    calc
      g r = (r * ‖actualOriginMatchedKummerSlope K a b F U DU r‖) ^ 2 := by
        dsimp [g]
        rw [hDeriv.deriv]
        ring
      _ ≤ Efull ^ 2 := by
        exact pow_le_pow_left₀ hNonneg
          (by simpa only [Efull] using hPoint) 2
  have hFinite : (volume : Measure ℝ) (Icc a b) < ⊤ := by
    simp only [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hAE : ∀ᵐ r : ℝ ∂volume, r ∈ Icc a b →
      ‖g r‖ ≤ Efull ^ 2 := by
    filter_upwards [hDerivativeAE] with r hr hrmem
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [g]; positivity)]
    exact hBound r hrmem (hr hrmem)
  have hNorm := norm_setIntegral_le_of_norm_le_const_ae'
    (μ := volume) (s := Icc a b) (f := g) (C := Efull ^ 2)
    hFinite hAE
  have hIntegral :
      ‖∫ r in Icc a b, g r‖ ≤ Efull ^ 2 * (b - a) := by
    simpa only [Real.volume_real_Icc_of_le hab] using hNorm
  calc
    (∫ r in Icc a b, r ^ 2 * ‖deriv W r‖ ^ 2) =
        ∫ r in Icc a b, g r := rfl
    _ ≤ ‖∫ r in Icc a b, g r‖ :=
      (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm
    _ ≤ Efull ^ 2 * (b - a) := hIntegral
    _ = (b - a) * Efull ^ 2 := by ring

end HBL.TypeIIDynamicSelection
