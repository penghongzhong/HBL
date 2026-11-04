import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCoupledCompatibility
import HBL.InnerReconstruction.UniformMomentOperatorBound

/-!
Quantitative physical traces of the two actual moment-locked inner responses.
The first-moment constants include the potential action on the normalized
Fredholm unknown and the affinely corrected physical source. Their weighted
norm bounds use constants derived from the fixed Fredholm operators.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- The uniquely forced minus-channel charge of the physical scale input. -/
def actualMomentLockedInnerScaleCharge (L c : ℝ) : ℝ :=
  actualMinusCharge (actualMomentLockedInnerScaleSource L c)

/-- The uniquely forced plus-channel charge of the physical phase input. -/
def actualMomentLockedInnerPhaseCharge (L c : ℝ) : ℝ :=
  actualPlusCharge (actualMomentLockedInnerPhaseSource L c)

def actualMomentLockedInnerScaleCorrectedSource (L c : ℝ) : ℝ → ℝ :=
  correctedMinusSource (actualMomentLockedInnerScaleSource L c)

def actualMomentLockedInnerPhaseCorrectedSource (L c : ℝ) : ℝ → ℝ :=
  correctedPlusSource (actualMomentLockedInnerPhaseSource L c)

theorem actual_Hartree_moment_locked_corrected_sources_weighted
    (L c : ℝ) (hL : 0 < L) :
    InWeightedL2 (7 / 4 : ℝ) (actualMomentLockedInnerScaleCorrectedSource L c) ∧
    InWeightedL2 (7 / 4 : ℝ) (actualMomentLockedInnerPhaseCorrectedSource L c) := by
  exact ⟨correctedMinusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) _
      (actual_Hartree_moment_locked_inner_scale_source_weighted L c hL),
    correctedPlusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) _
      (actual_Hartree_moment_locked_inner_phase_source_weighted L c hL)⟩

/-- The potential datum in the genuine minus-channel Green representative. -/
def actualMomentLockedInnerScaleGreenData (L c : ℝ) (hL : 0 < L) :
    RealL2 halfLineMeasure :=
  (3 : ℝ) • (normalizedMinusInner (7 / 4 : ℝ) (by norm_num) (by norm_num)
    (actualMomentLockedInnerScaleSource L c)
    (actual_Hartree_moment_locked_inner_scale_source_weighted L c hL) :
      RealL2 halfLineMeasure)

/-- The potential datum in the genuine plus-channel Green representative. -/
def actualMomentLockedInnerPhaseGreenData (L c : ℝ) (hL : 0 < L) :
    RealL2 halfLineMeasure :=
  weightedPotentialOperator (normalizedPlusInner (7 / 4 : ℝ)
    (by norm_num) (by norm_num) (actualMomentLockedInnerPhaseSource L c)
    (actual_Hartree_moment_locked_inner_phase_source_weighted L c hL))

def actualMomentLockedInnerScaleTotalSource (L c : ℝ) (hL : 0 < L) : ℝ → ℝ :=
  innerGreenTotalSource (actualMomentLockedInnerScaleGreenData L c hL)
    (actualMomentLockedInnerScaleCorrectedSource L c)

def actualMomentLockedInnerPhaseTotalSource (L c : ℝ) (hL : 0 < L) : ℝ → ℝ :=
  innerGreenTotalSource (actualMomentLockedInnerPhaseGreenData L c hL)
    (actualMomentLockedInnerPhaseCorrectedSource L c)

/-- M_b retains the potential contribution as well as the corrected input. -/
def actualMomentLockedInnerScaleMoment (L c : ℝ) (hL : 0 < L) : ℝ :=
  innerGreenBound (actualMomentLockedInnerScaleGreenData L c hL)
    (actualMomentLockedInnerScaleCorrectedSource L c)

/-- M_omega retains the potential contribution as well as the corrected input. -/
def actualMomentLockedInnerPhaseMoment (L c : ℝ) (hL : 0 < L) : ℝ :=
  innerGreenBound (actualMomentLockedInnerPhaseGreenData L c hL)
    (actualMomentLockedInnerPhaseCorrectedSource L c)

def actualMomentLockedInnerScaleCorrectedNorm (L c : ℝ) (hL : 0 < L) : ℝ :=
  ‖correctedMinusDataL2 (7 / 4 : ℝ) (by norm_num)
    (actualMomentLockedInnerScaleSource L c)
    (actual_Hartree_moment_locked_inner_scale_source_weighted L c hL)‖

def actualMomentLockedInnerPhaseCorrectedNorm (L c : ℝ) (hL : 0 < L) : ℝ :=
  ‖correctedPlusDataL2 (7 / 4 : ℝ) (by norm_num)
    (actualMomentLockedInnerPhaseSource L c)
    (actual_Hartree_moment_locked_inner_phase_source_weighted L c hL)‖

/-- Both real moment constants are nonnegative by their explicit integrals. -/
theorem actual_Hartree_moment_locked_response_moments_nonneg
    (L c : ℝ) (hL : 0 < L) :
    0 ≤ actualMomentLockedInnerScaleMoment L c hL ∧
    0 ≤ actualMomentLockedInnerPhaseMoment L c hL := by
  constructor <;>
    simp only [actualMomentLockedInnerScaleMoment, actualMomentLockedInnerPhaseMoment,
      innerGreenBound, weightedGreenPrimitiveBound] <;>
    exact add_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _)

/-- The total sources of the actual Green representatives have finite first
moments, bounded by the concrete M_b and M_omega above. -/
theorem actual_Hartree_moment_locked_response_total_source_firstMoment
    (L c : ℝ) (hL : 0 < L) :
    (Integrable (actualMomentLockedInnerScaleTotalSource L c hL) halfLineMeasure ∧
      Integrable (fun r => r * actualMomentLockedInnerScaleTotalSource L c hL r)
        halfLineMeasure ∧
      halfLineGreenAbsoluteFirstMoment (actualMomentLockedInnerScaleTotalSource L c hL) ≤
        actualMomentLockedInnerScaleMoment L c hL) ∧
    (Integrable (actualMomentLockedInnerPhaseTotalSource L c hL) halfLineMeasure ∧
      Integrable (fun r => r * actualMomentLockedInnerPhaseTotalSource L c hL r)
        halfLineMeasure ∧
      halfLineGreenAbsoluteFirstMoment (actualMomentLockedInnerPhaseTotalSource L c hL) ≤
        actualMomentLockedInnerPhaseMoment L c hL) := by
  have hb := innerGreenRepresentative_total_source_firstMoment
    (actualMomentLockedInnerScaleGreenData L c hL) (7 / 4 : ℝ) (by norm_num)
    (actualMomentLockedInnerScaleCorrectedSource L c)
    (actual_Hartree_moment_locked_corrected_sources_weighted L c hL).1
  have hw := innerGreenRepresentative_total_source_firstMoment
    (actualMomentLockedInnerPhaseGreenData L c hL) (7 / 4 : ℝ) (by norm_num)
    (actualMomentLockedInnerPhaseCorrectedSource L c)
    (actual_Hartree_moment_locked_corrected_sources_weighted L c hL).2
  exact ⟨⟨hb.1, hb.2.1, hb.2.2.2⟩, ⟨hw.1, hw.2.1, hw.2.2.2⟩⟩

/-- Physical q/r traces of the two actual fixed Fredholm responses, at any
radius beyond the affine cutoff. Source membership and first moments are
proved above; neither traces nor an inverse bound are hypotheses. -/
theorem actual_Hartree_moment_locked_response_trace_bounds
    (L c : ℝ) (hL : 0 < L) (r : ℝ) (hr : 2 < r) :
    let hb := actual_Hartree_moment_locked_inner_scale_source_weighted L c hL
    let hw := actual_Hartree_moment_locked_inner_phase_source_weighted L c hL
    |actualMomentLockedPhysicalMinus (actualMomentLockedInnerScaleSource L c) hb r -
      actualMomentLockedInnerScaleCharge L c| ≤
        actualMomentLockedInnerScaleMoment L c hL / r ∧
    |deriv (actualMomentLockedPhysicalMinus (actualMomentLockedInnerScaleSource L c) hb) r| ≤
        actualMomentLockedInnerScaleMoment L c hL / r ^ 2 ∧
    |actualMomentLockedPhysicalPlus (actualMomentLockedInnerPhaseSource L c) hw r -
      actualMomentLockedInnerPhaseCharge L c| ≤
        actualMomentLockedInnerPhaseMoment L c hL / r ∧
    |deriv (actualMomentLockedPhysicalPlus (actualMomentLockedInnerPhaseSource L c) hw) r| ≤
        actualMomentLockedInnerPhaseMoment L c hL / r ^ 2 := by
  dsimp only
  have hb := innerGreenRepresentative_affine_physical_trace_bounds
    (actualMomentLockedInnerScaleGreenData L c hL) (7 / 4 : ℝ) (by norm_num)
    (actualMomentLockedInnerScaleCorrectedSource L c)
    (actual_Hartree_moment_locked_corrected_sources_weighted L c hL).1
    (actualMomentLockedInnerScaleCharge L c) r hr
  have hw := innerGreenRepresentative_affine_physical_trace_bounds
    (actualMomentLockedInnerPhaseGreenData L c hL) (7 / 4 : ℝ) (by norm_num)
    (actualMomentLockedInnerPhaseCorrectedSource L c)
    (actual_Hartree_moment_locked_corrected_sources_weighted L c hL).2
    (actualMomentLockedInnerPhaseCharge L c) r hr
  exact ⟨hb.1, hb.2, hw.1, hw.2⟩

/-- The trace estimate at the actual moving inner interface rho=L. -/
theorem actual_Hartree_moment_locked_response_trace_at_cutoff
    (L c : ℝ) (hL : 2 < L) :
    let hLp : 0 < L := lt_trans (by norm_num : (0 : ℝ) < 2) hL
    let hb := actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp
    let hw := actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp
    |actualMomentLockedPhysicalMinus (actualMomentLockedInnerScaleSource L c) hb L -
      actualMomentLockedInnerScaleCharge L c| ≤
        actualMomentLockedInnerScaleMoment L c hLp / L ∧
    |deriv (actualMomentLockedPhysicalMinus (actualMomentLockedInnerScaleSource L c) hb) L| ≤
        actualMomentLockedInnerScaleMoment L c hLp / L ^ 2 ∧
    |actualMomentLockedPhysicalPlus (actualMomentLockedInnerPhaseSource L c) hw L -
      actualMomentLockedInnerPhaseCharge L c| ≤
        actualMomentLockedInnerPhaseMoment L c hLp / L ∧
    |deriv (actualMomentLockedPhysicalPlus (actualMomentLockedInnerPhaseSource L c) hw) L| ≤
        actualMomentLockedInnerPhaseMoment L c hLp / L ^ 2 :=
  actual_Hartree_moment_locked_response_trace_bounds L c
    (lt_trans (by norm_num : (0 : ℝ) < 2) hL) L hL

/-- A single constant, derived from the two fixed Fredholm inverses, controls
both true response moments by their corrected weighted source norms. The
constant is independent of the moving cutoff L and the locked amplitude c. -/
theorem actual_Hartree_moment_locked_response_fixed_moment_constant :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (L c : ℝ) (hL : 0 < L),
      actualMomentLockedInnerScaleMoment L c hL ≤
        D * actualMomentLockedInnerScaleCorrectedNorm L c hL ∧
      actualMomentLockedInnerPhaseMoment L c hL ≤
        D * actualMomentLockedInnerPhaseCorrectedNorm L c hL := by
  obtain ⟨Dp, Dm, hDp, _hDm, hBounds⟩ := actual_inner_fixed_Fredholm_moment_constants
  refine ⟨max Dp Dm, le_trans hDp (le_max_left _ _), ?_⟩
  intro L c hL
  let Fp := actualMomentLockedInnerPhaseSource L c
  let Fm := actualMomentLockedInnerScaleSource L c
  have hp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hL
  have hm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hL
  let x : InnerCorrections :=
    (normalizedPlusInner (7 / 4 : ℝ) (by norm_num) (by norm_num) Fp hp,
      normalizedMinusInner (7 / 4 : ℝ) (by norm_num) (by norm_num) Fm hm)
  have hxp := normalizedPlusInner_equation (7 / 4 : ℝ) (by norm_num) (by norm_num) Fp hp
  have hxm := normalizedMinusInner_equation (7 / 4 : ℝ) (by norm_num) (by norm_num) Fm hm
  have hBoth := hBounds (correctedPlusSource Fp) (correctedMinusSource Fm)
    (correctedPlusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) Fp hp)
    (correctedMinusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) Fm hm) x hxp hxm
  constructor
  · exact hBoth.2.trans (mul_le_mul_of_nonneg_right (le_max_right Dp Dm) (norm_nonneg _))
  · exact hBoth.1.trans (mul_le_mul_of_nonneg_right (le_max_left Dp Dm) (norm_nonneg _))

end HBL.TypeIIDynamicSelection
