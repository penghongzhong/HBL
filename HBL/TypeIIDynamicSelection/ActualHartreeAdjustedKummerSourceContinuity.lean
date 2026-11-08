import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedProjection
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedSpeed
import HBL.MonopoleMovingCutoffSpatial
import Mathlib.Tactic

/-!
# Actual moment-locked Hartree Kummer speed sources are continuous

The fully adjusted Kummer source is F - db*S - domega*P, where S and P
are the genuine moment-locked (not abstract) speed directions. We derive
their positive-radial continuity from the exact cutoff cancellation
and the original Green/Fredholm monopole regularity. Thus continuity
of the adjusted source follows solely from continuity of the genuine
unadjusted Hartree forcing, with no additional regularity imposed on
the independently selected speed.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_moment_locked_scale_profile_continuousAt
    (c r : ℝ) (hr : 0 < r) :
    ContinuousAt (actualMomentLockedScaleProfile c) r := by
  have hlog : Continuous (deriv monopoleLogModel) :=
    (contDiff_infty_iff_deriv.mp monopoleLogModel_contDiff_infty).2.continuous
  have hmodel : Continuous (deriv model) :=
    (contDiff_infty_iff_deriv.mp model_contDiff_infty).2.continuous
  have htail : ContinuousAt
      (halfLineGreenTail monopoleRemainderSource) r :=
    (halfLineGreenTail_hasDerivAt
      monopoleRemainderSource_continuous
      monopoleRemainderSource_integrable hr).continuousAt
  have hmono : ContinuousAt monopoleRadialProfile r :=
    (monopoleRadialProfile_hasDerivAt hr).continuousAt
  have hGreen : ContinuousAt
      (fun x : ℝ =>
        deriv monopoleLogModel x +
          monopoleAffineSlope * deriv model x +
          halfLineGreenTail monopoleRemainderSource x -
          monopoleRadialProfile x / 2) r := by
    exact ((hlog.continuousAt.add
      (continuousAt_const.mul hmodel.continuousAt)).add htail).sub
      (hmono.div_const 2)
  have hLocalGreen :
      dilationGenerator monopoleRadialProfile =ᶠ[𝓝 r]
        (fun x : ℝ =>
          deriv monopoleLogModel x +
          monopoleAffineSlope * deriv model x +
          halfLineGreenTail monopoleRemainderSource x -
          monopoleRadialProfile x / 2) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact monopoleRadialProfile_dilation_green_eq hx
  have hDil : ContinuousAt (dilationGenerator monopoleRadialProfile) r :=
    hGreen.congr_of_eventuallyEq hLocalGreen
  have hb : Continuous bubble := bubble_contDiff_infty.continuous
  have hdb : Continuous (deriv bubble) :=
    (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).2.continuous
  have hbDil : ContinuousAt (dilationGenerator bubble) r := by
    unfold dilationGenerator
    exact (hb.continuousAt.div_const 2).add
      (continuousAt_id.mul hdb.continuousAt)
  have hCut : Continuous (fun x : ℝ => cutoff (|c| * x / 4)) :=
    cutoff_contDiff_infty.continuous.comp
      ((continuous_const.mul continuous_id).div_const 4)
  have hModel : ContinuousAt
      (fun x : ℝ =>
        dilationGenerator bubble x +
          c * (1 - cutoff (|c| * x / 4)) *
            (dilationGenerator monopoleRadialProfile x -
              monopoleRadialProfile x)) r := by
    exact hbDil.add
      ((continuousAt_const.mul
        (continuousAt_const.sub hCut.continuousAt)).mul
        (hDil.sub hmono))
  have hNear :
      actualMomentLockedScaleProfile c =ᶠ[𝓝 r]
        (fun x : ℝ =>
          dilationGenerator bubble x +
            c * (1 - cutoff (|c| * x / 4)) *
              (dilationGenerator monopoleRadialProfile x -
                monopoleRadialProfile x)) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact actual_Hartree_moment_locked_scale_cutoff_cancellation c x hx
  exact hModel.congr_of_eventuallyEq hNear

/-- Local regularity for the entire ACTUAL adjusted Kummer source. The
two complex speed directions are the original scaled monopole forcing,
not arbitrary assumed continuous substitutes. -/
theorem actual_Hartree_adjusted_Kummer_source_continuousAt
    (a c r : ℝ) (ha : 0 < a) (hr : 0 < r)
    (F : ℝ → ℂ) (hF : ContinuousAt F r)
    (p : ℝ × ℝ) :
    ContinuousAt (fun x : ℝ =>
      F x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
        (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x) r := by
  have hArg : ContinuousAt (fun x : ℝ => a * x) r :=
    (continuous_const.mul continuous_id).continuousAt
  have hPos : 0 < a * r := mul_pos ha hr
  have hScale : ContinuousAt
      (fun x : ℝ => actualMomentLockedScaleProfile c (a * x)) r :=
    (actual_Hartree_moment_locked_scale_profile_continuousAt c (a * r) hPos).comp
      hArg
  have hCore : ContinuousAt
      (fun x : ℝ => actualMomentLockedCore c (a * x)) r :=
    (monopoleMovingCutoffSpatial_hasDerivAt c hPos).continuousAt.comp hArg
  have hRealScale : ContinuousAt
      (fun x : ℝ => (actualMomentLockedScaleProfile c (a * x) : ℂ)) r :=
    Complex.continuous_ofReal.continuousAt.comp hScale
  have hRealCore : ContinuousAt
      (fun x : ℝ => (actualMomentLockedCore c (a * x) : ℂ)) r :=
    Complex.continuous_ofReal.continuousAt.comp hCore
  have hS : ContinuousAt (actualMomentLockedScaledScaleSource a c) r := by
    unfold actualMomentLockedScaledScaleSource actualMomentLockedScaleSource
    exact continuousAt_const.mul (continuousAt_const.mul hRealScale)
  have hP : ContinuousAt (actualMomentLockedScaledPhaseSource a c) r := by
    unfold actualMomentLockedScaledPhaseSource actualMomentLockedPhaseSource
    exact continuousAt_const.mul hRealCore
  exact (hF.add (continuousAt_const.mul hS)).add
    (continuousAt_const.mul hP)

end HBL.TypeIIDynamicSelection
