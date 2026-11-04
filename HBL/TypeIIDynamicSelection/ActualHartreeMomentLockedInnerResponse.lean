import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedSpeed
import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedLocalizedInner
import HBL.InnerEstimates.PlusEquation
import HBL.InnerEstimates.MinusEquation
import HBL.InnerEstimates.PlusOutputProperties
import HBL.InnerEstimates.MinusOutputProperties
import HBL.InnerReconstruction.GreenC1Integrable
import HBL.InnerReconstruction.RepresentativeFirstMomentTrace
import Mathlib.Tactic

/-!
Two actual inner responses to the moment-locked scale and phase speeds.
The inputs are r*eta_R*Q_c and r*eta_R*V_c, with the same genuine radial
conjugation and partition used in the physical inner correction. Weighted
membership is proved from the physical profiles and finite support. The
responses reuse the fixed, normalized H-minus and H-plus inverses; their affine
charges are forced by the original resonance pairings. Physical traces
are those of q/r. No nonzero matching determinant or relative PDE residual
gain is asserted here.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

def actualMomentLockedInnerScaleSource (R c r : ℝ) : ℝ :=
  r * actualHartreeInnerSourceCutoff R r * actualMomentLockedScaleProfile c r

def actualMomentLockedInnerPhaseSource (R c r : ℝ) : ℝ :=
  r * actualHartreeInnerSourceCutoff R r * actualMomentLockedCore c r

/-- Exact radial localization of the two genuine physical directions. -/
theorem actual_Hartree_moment_locked_inner_source_identification (R c r : ℝ) :
    ((r * actualHartreeInnerSourceCutoff R r : ℝ) : ℂ) *
        actualMomentLockedScaleSource c r =
      Complex.I * (actualMomentLockedInnerScaleSource R c r : ℂ) ∧
    ((r * actualHartreeInnerSourceCutoff R r : ℝ) : ℂ) *
        actualMomentLockedPhaseSource c r =
      (actualMomentLockedInnerPhaseSource R c r : ℂ) := by
  constructor <;>
    dsimp [actualMomentLockedScaleSource, actualMomentLockedPhaseSource,
      actualMomentLockedInnerScaleSource, actualMomentLockedInnerPhaseSource] <;>
    push_cast <;> ring

/-- The original radial source is the sum of its inner and exterior pieces.
In particular the exterior piece is retained even when the matching radius
lies beyond the support of the inner cutoff. -/
theorem actual_Hartree_moment_locked_sources_exact_partition (R c r : ℝ) :
    (r : ℂ) * actualMomentLockedScaleSource c r =
      Complex.I * (actualMomentLockedInnerScaleSource R c r : ℂ) +
        ((r * cutoff (r / R) : ℝ) : ℂ) * actualMomentLockedScaleSource c r ∧
    (r : ℂ) * actualMomentLockedPhaseSource c r =
      (actualMomentLockedInnerPhaseSource R c r : ℂ) +
        ((r * cutoff (r / R) : ℝ) : ℂ) * actualMomentLockedPhaseSource c r := by
  constructor <;>
    dsimp [actualMomentLockedScaleSource, actualMomentLockedPhaseSource,
      actualMomentLockedInnerScaleSource, actualMomentLockedInnerPhaseSource,
      actualHartreeInnerSourceCutoff] <;>
    push_cast <;> ring

/-- On the actual inner region, the localized inputs equal r times the
original moment-locked physical speed directions. -/
theorem actual_Hartree_moment_locked_inner_sources_core
    (R c r : ℝ) (hR : 0 < R) (hr : r ∈ Ioc (0 : ℝ) R) :
    Complex.I * (actualMomentLockedInnerScaleSource R c r : ℂ) =
      (r : ℂ) * actualMomentLockedScaleSource c r ∧
    (actualMomentLockedInnerPhaseSource R c r : ℂ) =
      (r : ℂ) * actualMomentLockedPhaseSource c r := by
  have h := actual_Hartree_moment_locked_inner_source_identification R c r
  rw [actual_Hartree_inner_source_cutoff_one R r hR hr.2, mul_one] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- Past the inner support, the entire physical direction remains in the
exterior source; it has not disappeared from the original PDE. -/
theorem actual_Hartree_moment_locked_inner_sources_exterior
    (R c r : ℝ) (hR : 0 < R) (hr : 2 * R ≤ r) :
    actualMomentLockedInnerScaleSource R c r = 0 ∧
    actualMomentLockedInnerPhaseSource R c r = 0 ∧
    ((r * cutoff (r / R) : ℝ) : ℂ) * actualMomentLockedScaleSource c r =
      (r : ℂ) * actualMomentLockedScaleSource c r ∧
    ((r * cutoff (r / R) : ℝ) : ℂ) * actualMomentLockedPhaseSource c r =
      (r : ℂ) * actualMomentLockedPhaseSource c r := by
  have hCut := cutoff_one_of_two_le (r / R) ((le_div_iff₀ hR).2 hr)
  simp only [actualMomentLockedInnerScaleSource, actualMomentLockedInnerPhaseSource,
    actualHartreeInnerSourceCutoff, hCut, sub_self, mul_zero, zero_mul, mul_one,
    and_self]

private theorem actual_inner_speed_measurable (R c : ℝ) :
    Measurable (actualMomentLockedInnerScaleSource R c) ∧
    Measurable (actualMomentLockedInnerPhaseSource R c) := by
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
  have hCut : Measurable (actualHartreeInnerSourceCutoff R) :=
    (actual_Hartree_inner_source_cutoff_continuous R).measurable
  exact ⟨(measurable_id.mul hCut).mul hQ,
    (measurable_id.mul hCut).mul hCore⟩

private theorem positive_compact_weighted_source
    (R B : ℝ) (hR : 0 < R) (F : ℝ → ℝ) (hF : Measurable F)
    (hBound : ∀ r : ℝ, 0 < r → r ≤ 2 * R → |F r| ≤ B)
    (hZero : ∀ r : ℝ, 2 * R < r → F r = 0) :
    InWeightedL2 (7 / 4 : ℝ) F := by
  let A := affineJapaneseWeight (7 / 4 : ℝ) (2 * R) * |B|
  let S : ℝ → ℝ := fun r => affineJapaneseWeight (7 / 4 : ℝ) r * F r
  have hMeas : Measurable S := by
    exact (affineJapaneseWeight_continuous (7 / 4 : ℝ)).measurable.mul hF
  have hW (r : ℝ) (hr : 0 < r) (hcap : r ≤ 2 * R) :
      affineJapaneseWeight (7 / 4 : ℝ) r ≤
        affineJapaneseWeight (7 / 4 : ℝ) (2 * R) := by
    unfold affineJapaneseWeight
    apply Real.rpow_le_rpow (by positivity)
      (by nlinarith [sq_nonneg (2 * R - r)])
    norm_num
  have hDom : ∀ r : ℝ,
      ‖(Ioi (0 : ℝ)).indicator S r‖ ≤
        (Ioc (0 : ℝ) (2 * R)).indicator (fun _ : ℝ => A) r := by
    intro r
    by_cases hr : 0 < r
    · by_cases hcap : r ≤ 2 * R
      · rw [indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr),
          indicator_of_mem (show r ∈ Ioc (0 : ℝ) (2 * R) from ⟨hr,hcap⟩)]
        have hw : 0 ≤ affineJapaneseWeight (7 / 4 : ℝ) r := by
          unfold affineJapaneseWeight
          positivity
        change ‖affineJapaneseWeight (7 / 4 : ℝ) r * F r‖ ≤ A
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
        exact (mul_le_mul_of_nonneg_left ((hBound r hr hcap).trans (le_abs_self B)) hw).trans
          (mul_le_mul_of_nonneg_right (hW r hr hcap) (abs_nonneg B))
      · have hz := hZero r (lt_of_not_ge hcap)
        have hOut : r ∉ Ioc (0 : ℝ) (2 * R) := fun h => hcap h.2
        simp [hr, hOut, S, hz]
    · have hOut : r ∉ Ioc (0 : ℝ) (2 * R) := fun h => hr h.1
      simp [hr, hOut]
  have hMajor : MemLp ((Ioc (0 : ℝ) (2 * R)).indicator
      (fun _ : ℝ => A)) 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet A
      (.inr measure_Ioc_lt_top.ne)
  have hIndicator : MemLp ((Ioi (0 : ℝ)).indicator S) 2
      (volume : Measure ℝ) := hMajor.mono'
    (hMeas.indicator measurableSet_Ioi).aestronglyMeasurable
    (Filter.Eventually.of_forall hDom)
  change MemLp S 2 ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))
  exact (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mp hIndicator

/-- Both speed inputs belong to the original weighted Fredholm domain.
There is no assumed source membership and no extra free monopole speed. -/
theorem actual_Hartree_moment_locked_inner_sources_weighted
    (R c : ℝ) (hR : 0 < R) :
    InWeightedL2 (7 / 4 : ℝ) (actualMomentLockedInnerScaleSource R c) ∧
    InWeightedL2 (7 / 4 : ℝ) (actualMomentLockedInnerPhaseSource R c) := by
  obtain ⟨M,hM,hClose⟩ := actual_Hartree_moment_locked_speed_profiles_uniform_close
  have hdW : Continuous (deriv bubble) :=
    (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).2.continuous
  have hW : Continuous bubble := bubble_contDiff_infty.continuous
  have hRef : Continuous (fun r : ℝ =>
      |dilationGenerator bubble r| + |bubble r|) := by
    unfold dilationGenerator
    fun_prop
  obtain ⟨B,hBound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * R)) hRef.continuousOn
  have hProfile (r : ℝ) (hr : 0 < r) (hcap : r ≤ 2 * R) :
      |actualMomentLockedScaleProfile c r| ≤ M * |c| + |B| ∧
      |actualMomentLockedCore c r| ≤ M * |c| + |B| := by
    have hb := hBound r ⟨hr.le,hcap⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hb
    have hQ0 : |dilationGenerator bubble r| ≤ |B| := by
      linarith [abs_nonneg (bubble r), le_abs_self B]
    have hV0 : |bubble r| ≤ |B| := by
      linarith [abs_nonneg (dilationGenerator bubble r), le_abs_self B]
    constructor
    · have ht := abs_add_le
        (actualMomentLockedScaleProfile c r - dilationGenerator bubble r)
        (dilationGenerator bubble r)
      rw [sub_add_cancel] at ht
      exact ht.trans (add_le_add (hClose c r hr).1 hQ0)
    · have ht := abs_add_le (actualMomentLockedCore c r - bubble r) (bubble r)
      rw [sub_add_cancel] at ht
      exact ht.trans (add_le_add (hClose c r hr).2 hV0)
  have hInputs (r : ℝ) (hr : 0 < r) (hcap : r ≤ 2 * R) :
      |actualMomentLockedInnerScaleSource R c r| ≤ (2 * R) * (M * |c| + |B|) ∧
      |actualMomentLockedInnerPhaseSource R c r| ≤ (2 * R) * (M * |c| + |B|) := by
    have hMul := actual_Hartree_inner_radial_multiplier_bound R r hR hr
    constructor
    · unfold actualMomentLockedInnerScaleSource
      rw [abs_mul]
      exact mul_le_mul hMul (hProfile r hr hcap).1 (abs_nonneg _)
        (by positivity)
    · unfold actualMomentLockedInnerPhaseSource
      rw [abs_mul]
      exact mul_le_mul hMul (hProfile r hr hcap).2 (abs_nonneg _)
        (by positivity)
  have hZero (r : ℝ) (hr : 2 * R < r) :
      actualMomentLockedInnerScaleSource R c r = 0 ∧
      actualMomentLockedInnerPhaseSource R c r = 0 := by
    have hFar : 2 ≤ r / R := (le_div_iff₀ hR).2 hr.le
    have hCut : actualHartreeInnerSourceCutoff R r = 0 := by
      unfold actualHartreeInnerSourceCutoff
      rw [cutoff_one_of_two_le (r / R) hFar]
      ring
    simp only [actualMomentLockedInnerScaleSource,
      actualMomentLockedInnerPhaseSource, hCut, mul_zero, zero_mul, and_self]
  have hMeas := actual_inner_speed_measurable R c
  exact ⟨positive_compact_weighted_source R _ hR _ hMeas.1
      (fun r hr hc => (hInputs r hr hc).1) (fun r hr => (hZero r hr).1),
    positive_compact_weighted_source R _ hR _ hMeas.2
      (fun r hr hc => (hInputs r hr hc).2) (fun r hr => (hZero r hr).2)⟩

theorem actual_Hartree_moment_locked_inner_scale_source_weighted
    (R c : ℝ) (hR : 0 < R) :
    InWeightedL2 (7 / 4 : ℝ) (actualMomentLockedInnerScaleSource R c) :=
  (actual_Hartree_moment_locked_inner_sources_weighted R c hR).1

theorem actual_Hartree_moment_locked_inner_phase_source_weighted
    (R c : ℝ) (hR : 0 < R) :
    InWeightedL2 (7 / 4 : ℝ) (actualMomentLockedInnerPhaseSource R c) :=
  (actual_Hartree_moment_locked_inner_sources_weighted R c hR).2

/-- The conjugated response q_b; its physical direction is i*q_b/r. -/
def actualMomentLockedInnerScaleResponse (R c : ℝ) (hR : 0 < R) : ℝ → ℝ :=
  normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num)
    (actualMomentLockedInnerScaleSource R c)
    (actual_Hartree_moment_locked_inner_sources_weighted R c hR).1

/-- The conjugated response q_omega; its physical direction is q_omega/r. -/
def actualMomentLockedInnerPhaseResponse (R c : ℝ) (hR : 0 < R) : ℝ → ℝ :=
  normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num)
    (actualMomentLockedInnerPhaseSource R c)
    (actual_Hartree_moment_locked_inner_sources_weighted R c hR).2

/-- Both actual normalized inner responses solve the original fixed
Fredholm equations. The weighted memberships are derived above and the
corrected source retains its uniquely forced physical affine charge. -/
theorem actual_Hartree_moment_locked_inner_normalized_equations
    (R c : ℝ) (hR : 0 < R) :
    let Fb := actualMomentLockedInnerScaleSource R c
    let Fw := actualMomentLockedInnerPhaseSource R c
    let hb := actual_Hartree_moment_locked_inner_scale_source_weighted R c hR
    let hw := actual_Hartree_moment_locked_inner_phase_source_weighted R c hR
    (1 - weightedPhaseBirman)
        (normalizedMinusInner (7 / 4 : ℝ) (by norm_num) (by norm_num) Fb hb :
          RealL2 halfLineMeasure) =
      weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
        (correctedMinusDataL2 (7 / 4 : ℝ) (by norm_num) Fb hb) ∧
    (1 - weightedBirmanSchwingerOperator)
        (normalizedPlusInner (7 / 4 : ℝ) (by norm_num) (by norm_num) Fw hw :
          RealL2 halfLineMeasure) =
      weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
        (correctedPlusDataL2 (7 / 4 : ℝ) (by norm_num) Fw hw) := by
  dsimp only
  exact ⟨normalizedMinusInner_equation (7 / 4 : ℝ) (by norm_num) (by norm_num)
      _ (actual_Hartree_moment_locked_inner_scale_source_weighted R c hR),
    normalizedPlusInner_equation (7 / 4 : ℝ) (by norm_num) (by norm_num)
      _ (actual_Hartree_moment_locked_inner_phase_source_weighted R c hR)⟩

private theorem speed_representative_c1
    (g : RealL2 halfLineMeasure) (F : ℝ → ℝ)
    (hF : InWeightedL2 (7 / 4 : ℝ) F) :
    Differentiable ℝ (innerGreenRepresentative g F) ∧
      Continuous (deriv (innerGreenRepresentative g F)) := by
  have hG := halfLineMinGreen_C1_of_integrable
    (fun r : ℝ => weightedGreenDecay r * g r)
    (weightedGreen_source_integrable g)
  have hS := halfLineMinGreen_C1_of_integrable F
    (weightedSource_integrable (7 / 4 : ℝ) (by norm_num) F hF)
  let slope : ℝ → ℝ := fun r =>
    halfLineL1GreenSlope (fun t => weightedGreenDecay t * g t) r +
      halfLineL1GreenSlope F r
  have hDer (r : ℝ) : HasDerivAt (innerGreenRepresentative g F) (slope r) r :=
    (hG.1 r).add (hS.1 r)
  refine ⟨fun r => (hDer r).differentiableAt, ?_⟩
  have heq : deriv (innerGreenRepresentative g F) = slope :=
    funext fun r => (hDer r).deriv
  rw [heq]
  exact hG.2.add hS.2

private theorem speed_restore_c1
    (q : ℝ → ℝ) (a : ℝ)
    (hq : Differentiable ℝ q) (hdq : Continuous (deriv q)) :
    Differentiable ℝ (affineRestore q a) ∧
      Continuous (deriv (affineRestore q a)) := by
  have hm : Differentiable ℝ model :=
    (contDiff_infty_iff_deriv.mp model_contDiff_infty).1
  have hdm : Continuous (deriv model) :=
    (contDiff_infty_iff_deriv.mp model_contDiff_infty).2.continuous
  have hDer (r : ℝ) : HasDerivAt (affineRestore q a)
      (deriv q r + a * deriv model r) r :=
    (hq r).hasDerivAt.add ((hm r).hasDerivAt.const_mul a)
  refine ⟨fun r => (hDer r).differentiableAt, ?_⟩
  have heq : deriv (affineRestore q a) =
      (fun r => deriv q r + a * deriv model r) :=
    funext fun r => (hDer r).deriv
  rw [heq]
  exact hdq.add (hdm.const_mul a)

/-- Generic C1 output of the fixed plus-channel inverse for weighted forcing. -/
theorem normalizedPlusOutput_C1
    (F : ℝ → ℝ) (hF : InWeightedL2 (7 / 4 : ℝ) F) :
    Differentiable ℝ (normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF) ∧
      Continuous (deriv (normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF)) := by
  apply speed_restore_c1
  · exact (speed_representative_c1 _ _
      (correctedPlusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) F hF)).1
  · exact (speed_representative_c1 _ _
      (correctedPlusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) F hF)).2

/-- Generic C1 output of the fixed phase-channel inverse for weighted forcing. -/
theorem normalizedMinusOutput_C1
    (F : ℝ → ℝ) (hF : InWeightedL2 (7 / 4 : ℝ) F) :
    Differentiable ℝ (normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF) ∧
      Continuous (deriv (normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF)) := by
  apply speed_restore_c1
  · exact (speed_representative_c1 _ _
      (correctedMinusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) F hF)).1
  · exact (speed_representative_c1 _ _
      (correctedMinusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) F hF)).2

/-- These are the SAME normalized fixed inverses, with the uniquely forced
charges. The response and its physical C1 trace are no extra input. -/
theorem actual_Hartree_moment_locked_inner_responses_C1
    (R c : ℝ) (hR : 0 < R) :
    InnerAffineProperties (actualMomentLockedInnerScaleResponse R c hR)
      (actualMinusCharge (actualMomentLockedInnerScaleSource R c)) ∧
    InnerAffineProperties (actualMomentLockedInnerPhaseResponse R c hR)
      (actualPlusCharge (actualMomentLockedInnerPhaseSource R c)) ∧
    (Differentiable ℝ (actualMomentLockedInnerScaleResponse R c hR) ∧
      Continuous (deriv (actualMomentLockedInnerScaleResponse R c hR))) ∧
    (Differentiable ℝ (actualMomentLockedInnerPhaseResponse R c hR) ∧
      Continuous (deriv (actualMomentLockedInnerPhaseResponse R c hR))) := by
  have hSrc := actual_Hartree_moment_locked_inner_sources_weighted R c hR
  refine ⟨normalizedMinusOutput_properties (7 / 4 : ℝ) (by norm_num) (by norm_num) _ hSrc.1,
    normalizedPlusOutput_properties (7 / 4 : ℝ) (by norm_num) (by norm_num) _ hSrc.2, ?_, ?_⟩
  · exact normalizedMinusOutput_C1 _ hSrc.1
  · exact normalizedPlusOutput_C1 _ hSrc.2

/-- Physical derivative at the scaled interface. The spatial scale a
and the quotient q/r derivative are both retained explicitly. -/
theorem actual_Hartree_moment_locked_inner_physical_traces
    (R c : ℝ) (hR : 0 < R) (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => actualMomentLockedInnerScaleResponse R c hR (a * t) / (a * t))
      (a * ((a * r) * deriv (actualMomentLockedInnerScaleResponse R c hR) (a * r) -
        actualMomentLockedInnerScaleResponse R c hR (a * r)) / (a * r) ^ 2) r ∧
    HasDerivAt (fun t : ℝ => actualMomentLockedInnerPhaseResponse R c hR (a * t) / (a * t))
      (a * ((a * r) * deriv (actualMomentLockedInnerPhaseResponse R c hR) (a * r) -
        actualMomentLockedInnerPhaseResponse R c hR (a * r)) / (a * r) ^ 2) r := by
  have hC1 := actual_Hartree_moment_locked_inner_responses_C1 R c hR
  have hArg : HasDerivAt (fun t : ℝ => a * t) a r := by
    simpa using! (hasDerivAt_id r).const_mul a
  have hOne (q : ℝ → ℝ) (hq : Differentiable ℝ q) :
      HasDerivAt (fun t : ℝ => q (a * t) / (a * t))
        (a * ((a * r) * deriv q (a * r) - q (a * r)) / (a * r) ^ 2) r := by
    have hqDer := ((hq (a * r)).hasDerivAt.comp r hArg).div hArg (mul_pos ha hr).ne'
    change HasDerivAt (fun t : ℝ => q (a * t) / (a * t))
      ((deriv q (a * r) * a * (a * r) - q (a * r) * a) / (a * r) ^ 2) r at hqDer
    convert hqDer using 1; ring
  exact ⟨hOne _ hC1.2.2.1.1, hOne _ hC1.2.2.2.1⟩

end HBL.TypeIIDynamicSelection
