import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedSpeed
import HBL.TypeIIDynamicSelection.ActualOriginFiniteRankTransmission
import HBL.MonopoleCoreIntegrability
import Mathlib.Tactic

/-!
The actual real scale/phase source directions are projected through the
original origin-normalized Wronskian integral. The monopole amplitude is
moment-locked, not a new free parameter. Both source integrabilities are
PROVED, and both projected columns are O(c)-close to the actual bubble
columns. No nonzero physical determinant or parameter cancellation is
assumed concluded. Spatial scaling a^2 and the true source shapes remain.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.Kummer

def actualMomentLockedScaledScaleSource (a c r : ℝ) : ℂ :=
  (a ^ 2 : ℝ) * actualMomentLockedScaleSource c (a * r)

def actualMomentLockedScaledPhaseSource (a c r : ℝ) : ℂ :=
  (a ^ 2 : ℝ) * actualMomentLockedPhaseSource c (a * r)

/-- Columns from actual physical directions, not auxiliary normalized sources. -/
def actualMomentLockedProjectionColumns
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R a c : ℝ) : ℂ × ℂ :=
  (originGreenCoeffA K (2 * R) (actualMomentLockedScaledScaleSource a c) R,
   originGreenCoeffA K (2 * R) (actualMomentLockedScaledPhaseSource a c) R)

/-- The actual two-real-coordinate determinant that still must be verified. -/
def actualMomentLockedProjectionDeterminant
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R a c : ℝ) : ℝ :=
  let P := actualMomentLockedProjectionColumns K R a c
  P.1.re * P.2.im - P.2.re * P.1.im

private theorem actual_scaled_speed_measurable (a c : ℝ) :
    Measurable (actualMomentLockedScaledScaleSource a c) ∧
    Measurable (actualMomentLockedScaledPhaseSource a c) := by
  have hCore : Measurable (actualMomentLockedCore c) :=
    monopoleMovingCutoffProfile_measurable.comp (measurable_const.prodMk measurable_id)
  have hP : Measurable monopoleRadialProfile :=
    monopoleProfile_continuous.measurable.div measurable_id
  have hChi : Measurable cutoff := cutoff_contDiff_infty.continuous.measurable
  have hDChi : Measurable (deriv cutoff) := measurable_deriv cutoff
  have hT : Measurable (actualMomentLockedAmplitudeTangent c) := by
    unfold actualMomentLockedAmplitudeTangent
    fun_prop
  have hDCore : Measurable (deriv (actualMomentLockedCore c)) := measurable_deriv _
  have hQ : Measurable (actualMomentLockedScaleProfile c) := by
    unfold actualMomentLockedScaleProfile dilationGenerator
    fun_prop
  constructor
  · exact measurable_const.mul ((measurable_const.mul
      (Complex.measurable_ofReal.comp hQ)).comp (measurable_const.mul measurable_id))
  · exact measurable_const.mul ((Complex.measurable_ofReal.comp hCore).comp
      (measurable_const.mul measurable_id))

/-- Integrability of both actual directions on every positive annulus is
proved from their real profiles, not an additional analytical premise. -/
theorem actual_Hartree_moment_locked_scaled_speed_integrable
    (a c R : ℝ) (ha : 0 < a) (hR : 0 < R) :
    IntervalIntegrable (actualMomentLockedScaledScaleSource a c) volume R (2 * R) ∧
    IntervalIntegrable (actualMomentLockedScaledPhaseSource a c) volume R (2 * R) := by
  obtain ⟨M,hM,hClose⟩ := actual_Hartree_moment_locked_speed_profiles_uniform_close
  have hdW : Continuous (deriv bubble) :=
    (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).2.continuous
  have hW : Continuous bubble := bubble_contDiff_infty.continuous
  have hRef : Continuous (fun r : ℝ =>
      |dilationGenerator bubble (a * r)| + |bubble (a * r)|) := by
    unfold dilationGenerator
    fun_prop
  obtain ⟨B,hBound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc R (2 * R)) hRef.continuousOn
  have hBounds (r : ℝ) (hr : r ∈ Icc R (2 * R)) :
      ‖actualMomentLockedScaledScaleSource a c r‖ ≤ a ^ 2 * (M * |c| + B) ∧
      ‖actualMomentLockedScaledPhaseSource a c r‖ ≤ a ^ 2 * (M * |c| + B) := by
    have hr0 : 0 < a * r := mul_pos ha (hR.trans_le hr.1)
    have hB := hBound r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hB
    have hQ0 : |dilationGenerator bubble (a * r)| ≤ B := by
      linarith [abs_nonneg (bubble (a * r))]
    have hW0 : |bubble (a * r)| ≤ B := by
      linarith [abs_nonneg (dilationGenerator bubble (a * r))]
    have hQ : |actualMomentLockedScaleProfile c (a * r)| ≤ M * |c| + B := by
      have ht := abs_add_le
        (actualMomentLockedScaleProfile c (a * r) - dilationGenerator bubble (a * r))
        (dilationGenerator bubble (a * r))
      rw [sub_add_cancel] at ht
      exact ht.trans (_root_.add_le_add (hClose c (a * r) hr0).1 hQ0)
    have hV : |actualMomentLockedCore c (a * r)| ≤ M * |c| + B := by
      have ht := abs_add_le (actualMomentLockedCore c (a * r) - bubble (a * r))
        (bubble (a * r))
      rw [sub_add_cancel] at ht
      exact ht.trans (_root_.add_le_add (hClose c (a * r) hr0).2 hW0)
    constructor
    · simpa only [actualMomentLockedScaledScaleSource, actualMomentLockedScaleSource,
        norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg a)] using
        mul_le_mul_of_nonneg_left hQ (sq_nonneg a)
    · simpa only [actualMomentLockedScaledPhaseSource, actualMomentLockedPhaseSource,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg a)] using
        mul_le_mul_of_nonneg_left hV (sq_nonneg a)
  have hConst : IntervalIntegrable
      (fun _ : ℝ => a ^ 2 * (M * |c| + B)) volume R (2 * R) := intervalIntegrable_const
  have hm := actual_scaled_speed_measurable a c
  constructor
  · apply hConst.mono_fun' hm.1.aestronglyMeasurable.restrict
    rw [uIoc_of_le (by linarith : R ≤ 2 * R)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hBounds r ⟨hr.1.le,hr.2⟩).1
  · apply hConst.mono_fun' hm.2.aestronglyMeasurable.restrict
    rw [uIoc_of_le (by linarith : R ≤ 2 * R)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hBounds r ⟨hr.1.le,hr.2⟩).2

private theorem actual_projection_difference_bound
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hC : 0 ≤ C) (hK : OriginBasisOn K R (2 * R) C)
    (F G : ℝ → ℂ)
    (hF : IntervalIntegrable F volume R (2 * R))
    (hG : IntervalIntegrable G volume R (2 * R)) (M : ℝ) (hM : 0 ≤ M)
    (hFG : ∀ r ∈ Icc R (2 * R), ‖F r - G r‖ ≤ M) :
    ‖originGreenCoeffA K (2 * R) F R - originGreenCoeffA K (2 * R) G R‖ ≤
      C ^ 2 * M * R := by
  have hlin := actual_origin_source_coefficient_add_mul K hR hK F G hF hG (-1)
  have heq : originGreenCoeffA K (2 * R) (fun r => F r - G r) R =
      originGreenCoeffA K (2 * R) F R - originGreenCoeffA K (2 * R) G R := by
    simpa only [neg_one_mul, sub_eq_add_neg] using hlin
  rw [← heq]
  have hB := (originGreen_coefficients_norm_le K R (2 * R) C M hC hM hK
    (fun r => F r - G r) hFG (show R ∈ Icc R (2 * R) by constructor <;> linarith)).1
  convert hB using 1; ring

/-- The true columns approach the explicit bubble columns, with a fixed M
chosen before a,c. The true Wronskian and Laplacian scaling a^2 are retained. -/
theorem actual_Hartree_moment_locked_projection_columns_close
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hC : 0 ≤ C) (hK : OriginBasisOn K R (2 * R) C) :
    ∃ M : ℝ, 0 < M ∧ ∀ (a c : ℝ), 0 < a →
      ‖(actualMomentLockedProjectionColumns K R a c).1 -
        (actualMomentLockedProjectionColumns K R a 0).1‖ ≤
        (C ^ 2 * a ^ 2 * R * M) * |c| ∧
      ‖(actualMomentLockedProjectionColumns K R a c).2 -
        (actualMomentLockedProjectionColumns K R a 0).2‖ ≤
        (C ^ 2 * a ^ 2 * R * M) * |c| := by
  obtain ⟨M,hM,hClose⟩ := actual_Hartree_moment_locked_speed_profiles_uniform_close
  refine ⟨M,hM,?_⟩
  intro a c ha
  have hI := actual_Hartree_moment_locked_scaled_speed_integrable a c R ha hR
  have hI0 := actual_Hartree_moment_locked_scaled_speed_integrable a 0 R ha hR
  have hDiff (r : ℝ) (hr : r ∈ Icc R (2 * R)) :
      ‖actualMomentLockedScaledScaleSource a c r -
        actualMomentLockedScaledScaleSource a 0 r‖ ≤ a ^ 2 * M * |c| ∧
      ‖actualMomentLockedScaledPhaseSource a c r -
        actualMomentLockedScaledPhaseSource a 0 r‖ ≤ a ^ 2 * M * |c| := by
    have hr0 : 0 < a * r := mul_pos ha (hR.trans_le hr.1)
    have h0 := actual_Hartree_moment_locked_zero_reference (a * r) hr0
    constructor
    · have heq : actualMomentLockedScaledScaleSource a c r -
          actualMomentLockedScaledScaleSource a 0 r =
          (a ^ 2 : ℝ) * Complex.I *
            ((actualMomentLockedScaleProfile c (a * r) -
              dilationGenerator bubble (a * r) : ℝ) : ℂ) := by
        unfold actualMomentLockedScaledScaleSource
        rw [h0.1]
        unfold actualMomentLockedScaleSource
        push_cast
        ring
      rw [heq]
      simpa only [norm_mul, Complex.norm_I, mul_one, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a), mul_assoc] using
        mul_le_mul_of_nonneg_left (hClose c (a * r) hr0).1 (sq_nonneg a)
    · have heq : actualMomentLockedScaledPhaseSource a c r -
          actualMomentLockedScaledPhaseSource a 0 r =
          (a ^ 2 : ℝ) * ((actualMomentLockedCore c (a * r) - bubble (a * r) : ℝ) : ℂ) := by
        unfold actualMomentLockedScaledPhaseSource
        rw [h0.2]
        unfold actualMomentLockedPhaseSource
        push_cast
        ring
      rw [heq]
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg a), mul_assoc] using
        mul_le_mul_of_nonneg_left (hClose c (a * r) hr0).2 (sq_nonneg a)
  constructor
  · have h := actual_projection_difference_bound K hR hC hK
      (actualMomentLockedScaledScaleSource a c) (actualMomentLockedScaledScaleSource a 0)
      hI.1 hI0.1 (a ^ 2 * M * |c|) (by positivity) (fun r hr => (hDiff r hr).1)
    exact h.trans_eq (by ring)
  · have h := actual_projection_difference_bound K hR hC hK
      (actualMomentLockedScaledPhaseSource a c) (actualMomentLockedScaledPhaseSource a 0)
      hI.2 hI0.2 (a ^ 2 * M * |c|) (by positivity) (fun r hr => (hDiff r hr).2)
    exact h.trans_eq (by ring)

/-- Exact response to REAL physical speed increments at a fixed instantaneous
configuration. This is not the full Jacobian of the coupled inner/Kummer map. -/
theorem actual_Hartree_moment_locked_compatibility_speed_response
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2 * R) C)
    (a c : ℝ) (ha : 0 < a) (F : ℝ → ℂ)
    (hF : IntervalIntegrable F volume R (2 * R)) (U DU : ℂ) (db dw : ℝ) :
    actualOriginTransmissionObstruction K R
      (fun r => F r + (db : ℂ) * actualMomentLockedScaledScaleSource a c r +
        (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r) U DU =
      actualOriginTransmissionObstruction K R F U DU -
        (db : ℂ) * (actualMomentLockedProjectionColumns K R a c).1 -
        (dw : ℂ) * (actualMomentLockedProjectionColumns K R a c).2 := by
  have hI := actual_Hartree_moment_locked_scaled_speed_integrable a c R ha hR
  have hFirst := actual_origin_source_coefficient_add_mul K hR hK F
    (actualMomentLockedScaledScaleSource a c) hF hI.1 (db : ℂ)
  have hSecond := actual_origin_source_coefficient_add_mul K hR hK
    (fun r => F r + (db : ℂ) * actualMomentLockedScaledScaleSource a c r)
    (actualMomentLockedScaledPhaseSource a c)
    (hF.add (hI.1.const_mul (db : ℂ))) hI.2 (dw : ℂ)
  unfold actualOriginTransmissionObstruction
  rw [hSecond,hFirst]
  unfold actualMomentLockedProjectionColumns
  ring

end HBL.TypeIIDynamicSelection
