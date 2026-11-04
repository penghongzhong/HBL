import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedProjection
import HBL.KummerOriginBasis.ReferenceIntegralLowerBound
import Mathlib.Tactic

/-!
Full-interval normalized projections of the ACTUAL moment-locked scale and
phase sources. The lower endpoint is L/a and the reference integral is the
actual origin Kummer integral on [0,B]. The error is derived from the exact
Wronskian, the explicit bubble tails, and the proved uniform O(|c|) profile
error. The elementary supremum estimates deliberately give a slightly
larger, logarithm-free error that tends to zero when L grows and L/a shrinks.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.Kummer

private def projectionReferenceDensity {mu theta scale : ℝ}
    (K : OriginKummerPair mu theta scale) (r : ℝ) : ℂ :=
  K.x r * Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4)

private theorem projectionReferenceDensity_norm {mu theta scale : ℝ}
    (K : OriginKummerPair mu theta scale) (r : ℝ) :
    ‖projectionReferenceDensity K r‖ = ‖K.x r‖ := by
  have he : ‖Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  simp only [projectionReferenceDensity, norm_mul, he, mul_one]

/-- Both actual bubble tails have a common explicit inverse-square bound. -/
private theorem bubble_two_speed_tail (L t : ℝ) (hL : 0 < L) (ht : L ≤ t) :
    |t * bubble t - 1| ≤ 2 / L ^ 2 ∧
      |t * dilationGenerator bubble t + 1 / 2| ≤ 2 / L ^ 2 := by
  have ht0 : 0 < t := hL.trans_le ht
  let w := bubble t
  have hw : 0 < w := by dsimp [w, bubble]; positivity
  have hs : 0 < Real.sqrt (1 + t ^ 2) := by positivity
  have hs2 : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hts : t ≤ Real.sqrt (1 + t ^ 2) := by
    rw [Real.le_sqrt ht0.le (by positivity)]
    linarith
  have htw : t * w ≤ 1 := by
    change t / Real.sqrt (1 + t ^ 2) ≤ 1
    exact (div_le_iff₀ hs).2 (by simpa using hts)
  have htw0 : 0 ≤ t * w := mul_nonneg ht0.le hw.le
  have hw2 : w ^ 2 = (1 + t ^ 2)⁻¹ := by
    dsimp [w, bubble]
    rw [inv_pow, hs2]
  have hw2bound : w ^ 2 ≤ 1 / L ^ 2 := by
    rw [hw2, ← one_div]
    apply one_div_le_one_div_of_le (sq_pos_of_pos hL)
    nlinarith
  have hidentity : (t * w) ^ 2 + w ^ 2 = 1 := by
    rw [mul_pow, hw2]
    field_simp [show 1 + t ^ 2 ≠ 0 by positivity]
    <;> ring
  have hmissing0 : 0 ≤ 1 - t * w := sub_nonneg.mpr htw
  have hmissing : 1 - t * w ≤ w ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htw) htw0]
  have hphase : |t * w - 1| ≤ 1 / L ^ 2 := by
    rw [abs_of_nonpos (by linarith : t * w - 1 ≤ 0)]
    have hh := hmissing.trans hw2bound
    linarith
  have hscale : dilationGenerator bubble t = -w / 2 + w ^ 3 := by
    rw [dilationGenerator_bubble_closed]
    dsimp [w, bubble]
    field_simp [hs.ne']
    <;> nlinarith only [hs2]
  have hscaleId : t * dilationGenerator bubble t + 1 / 2 =
      (1 - t * w) / 2 + (t * w) * w ^ 2 := by rw [hscale]; ring
  have hprod : (t * w) * w ^ 2 ≤ w ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right htw (sq_nonneg w)
  have hinv : 0 ≤ 1 / L ^ 2 := by positivity
  constructor
  · change |t * w - 1| ≤ _
    exact hphase.trans
      (div_le_div_of_nonneg_right (by norm_num) (sq_nonneg L))
  · rw [hscaleId, abs_of_nonneg (add_nonneg
      (div_nonneg hmissing0 (by norm_num)) (mul_nonneg htw0 (sq_nonneg w)))]
    have hm := hmissing.trans hw2bound
    have hp := hprod.trans hw2bound
    have hhalf : (1 - t * w) / 2 ≤ 1 / L ^ 2 :=
      (div_le_div_of_nonneg_right hm (by norm_num : (0 : ℝ) ≤ 2)).trans
        (div_le_self hinv (by norm_num : (1 : ℝ) ≤ 2))
    calc
      _ ≤ 1 / L ^ 2 + 1 / L ^ 2 := _root_.add_le_add hhalf hp
      _ = 2 / L ^ 2 := by rw [← add_div]; norm_num

private theorem actual_two_speed_tail (L t c M : ℝ) (hL : 0 < L) (ht : L ≤ t)
    (hClose :
      |actualMomentLockedScaleProfile c t - dilationGenerator bubble t| ≤ M * |c| ∧
      |actualMomentLockedCore c t - bubble t| ≤ M * |c|) :
    |t * actualMomentLockedScaleProfile c t + 1 / 2| ≤
        t * M * |c| + 2 / L ^ 2 ∧
      |t * actualMomentLockedCore c t - 1| ≤ t * M * |c| + 2 / L ^ 2 := by
  have ht0 : 0 < t := hL.trans_le ht
  have hTail := bubble_two_speed_tail L t hL ht
  constructor
  · calc
      _ = |t * (actualMomentLockedScaleProfile c t - dilationGenerator bubble t) +
          (t * dilationGenerator bubble t + 1 / 2)| := by congr 1; ring
      _ ≤ |t * (actualMomentLockedScaleProfile c t - dilationGenerator bubble t)| +
          |t * dilationGenerator bubble t + 1 / 2| := abs_add_le _ _
      _ ≤ t * (M * |c|) + 2 / L ^ 2 := by
        rw [abs_mul, abs_of_pos ht0]
        exact add_le_add (mul_le_mul_of_nonneg_left hClose.1 ht0.le) hTail.2
      _ = _ := by ring
  · calc
      _ = |t * (actualMomentLockedCore c t - bubble t) +
          (t * bubble t - 1)| := by congr 1; ring
      _ ≤ |t * (actualMomentLockedCore c t - bubble t)| +
          |t * bubble t - 1| := abs_add_le _ _
      _ ≤ t * (M * |c|) + 2 / L ^ 2 := by
        rw [abs_mul, abs_of_pos ht0]
        exact add_le_add (mul_le_mul_of_nonneg_left hClose.2 ht0.le) hTail.1
      _ = _ := by ring

private theorem origin_source_exact_reference_density
    {mu theta scale r0 B C r : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K r0 B C) (F : ℝ → ℂ)
    (hr : r ∈ Icc r0 B) (hr0 : 0 < r) :
    originGreenSourceA K F r = projectionReferenceDensity K r * (r : ℂ) * F r := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  rw [originGreenSourceA, originPhysicalValue, originGreenWronskian_exact K hK hr]
  rw [show -Complex.I * (r : ℂ) ^ 2 / 4 =
      -(Complex.I * (r : ℂ) ^ 2 / 4) by ring, Complex.exp_neg]
  dsimp [projectionReferenceDensity]
  field_simp [hrC, Complex.exp_ne_zero]

private theorem normalized_projection_error_from_density
    {mu theta scale r0 B C C0 : ℝ} (K : OriginKummerPair mu theta scale)
    (hr0 : 0 < r0) (horder : r0 ≤ B) (hBscale : B ≤ scale)
    (hC0 : 0 ≤ C0) (hK : OriginBasisOn K r0 B C)
    (hx : ∀ r ∈ Icc 0 B, ‖K.x r‖ ≤ C0 * r)
    (a : ℝ) (F : ℝ → ℂ) (hF : IntervalIntegrable F volume r0 B)
    (k : ℂ) (hk : ‖k‖ ≤ 1) (e : ℝ) (he : 0 ≤ e)
    (hError : ∀ r ∈ Icc r0 B,
      ‖(a : ℂ)⁻¹ * originGreenSourceA K F r - k * projectionReferenceDensity K r‖ ≤ e) :
    ‖(a : ℂ)⁻¹ * originGreenCoeffA K B F r0 -
        k * originKummerReferenceIntegral K B‖ ≤ C0 * r0 ^ 2 + e * B := by
  have hxC : ContinuousOn K.x (Icc 0 scale) :=
    fun r hr => (K.x_deriv r hr).continuousWithinAt
  have hpC : Continuous (fun r : ℝ =>
      Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4)) := by fun_prop
  have hqC : ContinuousOn (projectionReferenceDensity K) (Icc 0 B) :=
    (hxC.mono (Icc_subset_Icc_right hBscale)).mul hpC.continuousOn
  have hq0 : IntervalIntegrable (projectionReferenceDensity K) volume 0 r0 :=
    (hqC.mono (Icc_subset_Icc_right horder)).intervalIntegrable_of_Icc hr0.le
  have hq1 : IntervalIntegrable (projectionReferenceDensity K) volume r0 B :=
    (hqC.mono (Icc_subset_Icc_left hr0.le)).intervalIntegrable_of_Icc horder
  have hsplit : (∫ r in 0..r0, projectionReferenceDensity K r) +
      (∫ r in r0..B, projectionReferenceDensity K r) =
        originKummerReferenceIntegral K B :=
    intervalIntegral.integral_add_adjacent_intervals hq0 hq1
  have hf := ((actual_origin_Green_source_integrability K hK horder F hF).1).const_mul
    ((a : ℂ)⁻¹)
  have hdiff : (∫ r in r0..B,
      (a : ℂ)⁻¹ * originGreenSourceA K F r - k * projectionReferenceDensity K r) =
      (a : ℂ)⁻¹ * originGreenCoeffA K B F r0 -
        k * (∫ r in r0..B, projectionReferenceDensity K r) := by
    unfold originGreenCoeffA
    rw [intervalIntegral.integral_sub hf (hq1.const_mul k),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have heq : (a : ℂ)⁻¹ * originGreenCoeffA K B F r0 -
      k * originKummerReferenceIntegral K B =
      (∫ r in r0..B,
        (a : ℂ)⁻¹ * originGreenSourceA K F r - k * projectionReferenceDensity K r) -
        k * (∫ r in 0..r0, projectionReferenceDensity K r) := by
    rw [hdiff, ← hsplit]
    ring
  have hsmall : ‖∫ r in 0..r0, projectionReferenceDensity K r‖ ≤ C0 * r0 ^ 2 := by
    have hh : ‖∫ r in 0..r0, projectionReferenceDensity K r‖ ≤
        (C0 * r0) * |r0 - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro r hr
      rw [uIoc_of_le hr0.le] at hr
      rw [projectionReferenceDensity_norm]
      exact (hx r ⟨hr.1.le, hr.2.trans horder⟩).trans
        (mul_le_mul_of_nonneg_left hr.2 hC0)
    simpa only [sub_zero, abs_of_pos hr0, pow_two, mul_assoc] using hh
  have hmain : ‖∫ r in r0..B,
      (a : ℂ)⁻¹ * originGreenSourceA K F r - k * projectionReferenceDensity K r‖ ≤
        e * B := by
    have hh : ‖∫ r in r0..B,
        (a : ℂ)⁻¹ * originGreenSourceA K F r - k * projectionReferenceDensity K r‖ ≤
          e * |B - r0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro r hr
      rw [uIoc_of_le horder] at hr
      exact hError r ⟨hr.1.le, hr.2⟩
    rw [abs_of_nonneg (sub_nonneg.mpr horder)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith) he)
  rw [heq]
  calc
    _ ≤ ‖∫ r in r0..B,
        (a : ℂ)⁻¹ * originGreenSourceA K F r - k * projectionReferenceDensity K r‖ +
        ‖k * (∫ r in 0..r0, projectionReferenceDensity K r)‖ := norm_sub_le _ _
    _ ≤ e * B + C0 * r0 ^ 2 := by
      apply add_le_add hmain
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul hk hsmall (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by ring

/-- One fixed physical source constant controls both complete normalized
projection columns. The error consists of the missing origin interval,
the actual bubble tail on [L/a,B], and the actual moment-locked perturbation.
In particular, no projection-closeness hypothesis is assumed. -/
theorem actual_Hartree_moment_locked_full_projection_asymptotics_of_uniform_close
    (M : ℝ) (hM : 0 < M)
    (hClose : ∀ c r : ℝ, 0 < r →
      |actualMomentLockedScaleProfile c r - dilationGenerator bubble r| ≤ M * |c| ∧
      |actualMomentLockedCore c r - bubble r| ≤ M * |c|)
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a L B C C0 c : ℝ)
    (ha : 0 < a) (hL : 0 < L) (horder : L / a ≤ B) (hBscale : B ≤ scale)
    (hC0 : 0 ≤ C0) (hK : OriginBasisOn K (L / a) B C)
    (hx : ∀ r ∈ Icc 0 B, ‖K.x r‖ ≤ C0 * r) :
    ‖(a : ℂ)⁻¹ * originGreenCoeffA K B
        (actualMomentLockedScaledScaleSource a c) (L / a) +
          Complex.I * originKummerReferenceIntegral K B / 2‖ ≤
      C0 * L ^ 2 / a ^ 2 + 2 * C0 * B ^ 2 / L ^ 2 +
        C0 * M * B ^ 3 * (a * |c|) ∧
    ‖(a : ℂ)⁻¹ * originGreenCoeffA K B
        (actualMomentLockedScaledPhaseSource a c) (L / a) -
          originKummerReferenceIntegral K B‖ ≤
      C0 * L ^ 2 / a ^ 2 + 2 * C0 * B ^ 2 / L ^ 2 +
        C0 * M * B ^ 3 * (a * |c|) := by
  have hr0 : 0 < L / a := div_pos hL ha
  have hB : 0 < B := hr0.trans_le horder
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  let e : ℝ := C0 * B * (a * B * M * |c| + 2 / L ^ 2)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hprofile (r : ℝ) (hr : r ∈ Icc (L / a) B) :
      |a * r * actualMomentLockedScaleProfile c (a * r) + 1 / 2| ≤
          a * B * M * |c| + 2 / L ^ 2 ∧
        |a * r * actualMomentLockedCore c (a * r) - 1| ≤
          a * B * M * |c| + 2 / L ^ 2 := by
    have hrpos : 0 < r := hr0.trans_le hr.1
    have ht : L ≤ a * r := by
      have hh := (div_le_iff₀ ha).1 hr.1
      nlinarith
    have hh := actual_two_speed_tail L (a * r) c M hL ht
      (hClose c (a * r) (mul_pos ha hrpos))
    have hup : a * r * M * |c| + 2 / L ^ 2 ≤
        a * B * M * |c| + 2 / L ^ 2 := by
      gcongr
      exact hr.2
    exact ⟨hh.1.trans hup, hh.2.trans hup⟩
  have hq (r : ℝ) (hr : r ∈ Icc (L / a) B) :
      ‖projectionReferenceDensity K r‖ ≤ C0 * B := by
    rw [projectionReferenceDensity_norm]
    exact (hx r ⟨(hr0.trans_le hr.1).le, hr.2⟩).trans
      (mul_le_mul_of_nonneg_left hr.2 hC0)
  have hscale (r : ℝ) (hr : r ∈ Icc (L / a) B) :
      ‖(a : ℂ)⁻¹ * originGreenSourceA K (actualMomentLockedScaledScaleSource a c) r -
        (-Complex.I / 2) * projectionReferenceDensity K r‖ ≤ e := by
    have hEq : (a : ℂ)⁻¹ *
        originGreenSourceA K (actualMomentLockedScaledScaleSource a c) r -
          (-Complex.I / 2) * projectionReferenceDensity K r =
        projectionReferenceDensity K r * Complex.I *
          ((a * r * actualMomentLockedScaleProfile c (a * r) + 1 / 2 : ℝ) : ℂ) := by
      rw [origin_source_exact_reference_density K hK _ hr (hr0.trans_le hr.1)]
      unfold actualMomentLockedScaledScaleSource actualMomentLockedScaleSource
      push_cast
      field_simp [haC]
      <;> ring
    rw [hEq, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hq r hr) (hprofile r hr).1 (abs_nonneg _)
      (mul_nonneg hC0 hB.le)
  have hphase (r : ℝ) (hr : r ∈ Icc (L / a) B) :
      ‖(a : ℂ)⁻¹ * originGreenSourceA K (actualMomentLockedScaledPhaseSource a c) r -
        (1 : ℂ) * projectionReferenceDensity K r‖ ≤ e := by
    have hEq : (a : ℂ)⁻¹ *
        originGreenSourceA K (actualMomentLockedScaledPhaseSource a c) r -
          (1 : ℂ) * projectionReferenceDensity K r =
        projectionReferenceDensity K r *
          ((a * r * actualMomentLockedCore c (a * r) - 1 : ℝ) : ℂ) := by
      rw [origin_source_exact_reference_density K hK _ hr (hr0.trans_le hr.1)]
      unfold actualMomentLockedScaledPhaseSource actualMomentLockedPhaseSource
      push_cast
      field_simp [haC]
      <;> ring
    rw [hEq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hq r hr) (hprofile r hr).2 (abs_nonneg _)
      (mul_nonneg hC0 hB.le)
  have hFs := actual_Hartree_moment_locked_scaled_speed_integrable_on
    a c (L / a) B ha hr0 horder
  have hk : ‖(-Complex.I / 2 : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_neg, Complex.norm_I]
    norm_num
  have hb := normalized_projection_error_from_density K hr0 horder hBscale hC0 hK hx
    a (actualMomentLockedScaledScaleSource a c) hFs.1 (-Complex.I / 2) hk e he hscale
  have hw := normalized_projection_error_from_density K hr0 horder hBscale hC0 hK hx
    a (actualMomentLockedScaledPhaseSource a c) hFs.2 1 (by norm_num) e he hphase
  have hE : C0 * (L / a) ^ 2 + e * B =
      C0 * L ^ 2 / a ^ 2 + 2 * C0 * B ^ 2 / L ^ 2 +
        C0 * M * B ^ 3 * (a * |c|) := by dsimp [e]; ring
  rw [hE] at hb hw
  constructor
  · convert hb using 1 <;> congr 1 <;> ring
  · simpa only [one_mul] using hw

/-- The physical source constant is obtained before any Kummer parameters,
scaling, cutoff radius, or monopole amplitude is chosen. -/
theorem actual_Hartree_moment_locked_full_projection_asymptotics :
    ∃ Msrc : ℝ, 0 < Msrc ∧
      ∀ (mu theta scale : ℝ) (K : OriginKummerPair mu theta scale)
        (a L B C C0 c : ℝ),
        0 < a → 0 < L → L / a ≤ B → B ≤ scale → 0 ≤ C0 →
        OriginBasisOn K (L / a) B C →
        (∀ r ∈ Icc 0 B, ‖K.x r‖ ≤ C0 * r) →
        ‖(a : ℂ)⁻¹ * originGreenCoeffA K B
            (actualMomentLockedScaledScaleSource a c) (L / a) +
              Complex.I * originKummerReferenceIntegral K B / 2‖ ≤
          C0 * L ^ 2 / a ^ 2 + 2 * C0 * B ^ 2 / L ^ 2 +
            C0 * Msrc * B ^ 3 * (a * |c|) ∧
        ‖(a : ℂ)⁻¹ * originGreenCoeffA K B
            (actualMomentLockedScaledPhaseSource a c) (L / a) -
              originKummerReferenceIntegral K B‖ ≤
          C0 * L ^ 2 / a ^ 2 + 2 * C0 * B ^ 2 / L ^ 2 +
            C0 * Msrc * B ^ 3 * (a * |c|) := by
  obtain ⟨M, hM, hClose⟩ := actual_Hartree_moment_locked_speed_profiles_uniform_close
  refine ⟨M, hM, ?_⟩
  intro mu theta scale K a L B C C0 c ha hL horder hBscale hC0 hK hx
  exact actual_Hartree_moment_locked_full_projection_asymptotics_of_uniform_close
    M hM hClose K a L B C C0 c ha hL horder hBscale hC0 hK hx

end HBL.TypeIIDynamicSelection
