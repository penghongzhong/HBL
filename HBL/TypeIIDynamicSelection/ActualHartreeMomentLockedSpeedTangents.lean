import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedProjection
import HBL.MonopoleMovingCutoffTime
import Mathlib.Tactic

/-!
# Time tangents of the actual moment-locked scale and phase sources

The two compatibility directions are not fixed abstract functions: their
physical shapes depend on the moment-locked amplitude c(s). This file
differentiates those genuine shapes, including through c=0.

For the scale direction we first use the already proved cutoff-cancellation
identity
  Q_c = Lambda W + c (1-chi(|c|r/4)) (Lambda P-P),
so the apparent absolute-value singularity at c=0 is canceled by the leading
factor c.  The phase direction is the actual moving monopole itself and reuses
the globally valid moving-cutoff time derivative.

The final two statements keep the spatial scale a fixed.  The additional
a(s)-variation is a separate chain-rule term and is not hidden here.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualMomentLockedScaleProfileParameterTangent (c r : ℝ) : ℝ :=
  (1 - cutoff (|c| * r / 4) -
      (|c| * r / 4) * deriv cutoff (|c| * r / 4)) *
    (dilationGenerator monopoleRadialProfile r - monopoleRadialProfile r)

theorem actual_Hartree_moment_locked_scale_profile_parameter_hasDerivAt
    (c r : ℝ) (hr : 0 < r) :
    HasDerivAt
      (fun a : ℝ => actualMomentLockedScaleProfile a r)
      (actualMomentLockedScaleProfileParameterTangent c r) c := by
  let H : ℝ :=
    dilationGenerator monopoleRadialProfile r - monopoleRadialProfile r
  by_cases hc : c = 0
  · subst c
    have harg : ContinuousAt (fun a : ℝ => |a| * r / 4) 0 := by
      fun_prop
    have hz : |(0 : ℝ)| * r / 4 < 1 := by norm_num
    have hev := harg.eventually (Iio_mem_nhds hz)
    have hmodel :
        HasDerivAt (fun a : ℝ => dilationGenerator bubble r + a * H) H 0 := by
      have h :=
        (hasDerivAt_const (0 : ℝ) (dilationGenerator bubble r)).add
          ((hasDerivAt_id (0 : ℝ)).mul_const H)
      convert h using 1
      · funext a
        simp only [Pi.add_apply, Pi.mul_apply, id_eq]
      · ring
    have htarget :
        actualMomentLockedScaleProfileParameterTangent 0 r = H := by
      dsimp [actualMomentLockedScaleProfileParameterTangent, H]
      have hcut0 : cutoff 0 = 0 :=
        cutoff_zero_of_le_one 0 (by norm_num)
      simp only [abs_zero, zero_mul, zero_div, hcut0, sub_zero, one_mul]
      ring
    rw [htarget]
    apply hmodel.congr_of_eventuallyEq
    filter_upwards [hev] with a ha
    rw [actual_Hartree_moment_locked_scale_cutoff_cancellation a r hr,
      cutoff_zero_of_le_one _ ha.le]
    dsimp [H]
    ring
  · have habs : HasDerivAt (fun a : ℝ => |a|) (|c| / c) c := by
      rcases lt_or_gt_of_ne hc with hn | hp
      · have hneg : HasDerivAt (fun a : ℝ => |a|) (-1) c := by
          apply (hasDerivAt_neg c).congr_of_eventuallyEq
          filter_upwards [Iio_mem_nhds hn] with a ha
          exact abs_of_neg ha
        convert hneg using 1
        rw [abs_of_neg hn]
        field_simp [hc]
      · have hpos : HasDerivAt (fun a : ℝ => |a|) 1 c := by
          apply (hasDerivAt_id c).congr_of_eventuallyEq
          filter_upwards [Ioi_mem_nhds hp] with a ha
          exact abs_of_pos ha
        convert hpos using 1
        rw [abs_of_pos hp, div_self hc]
    have harg := (habs.mul_const r).div_const 4
    have hcut :=
      ((contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).1
        (|c| * r / 4)).hasDerivAt.comp c harg
    have heta := (hasDerivAt_const c (1 : ℝ)).sub hcut
    have hprod := (hasDerivAt_id c).mul heta
    have hmodel :=
      (hasDerivAt_const c (dilationGenerator bubble r)).add
        (hprod.mul_const H)
    convert hmodel using 1
    · funext a
      rw [actual_Hartree_moment_locked_scale_cutoff_cancellation a r hr]
      rfl
    · dsimp [actualMomentLockedScaleProfileParameterTangent, H]
      simp only [zero_add, one_mul, zero_sub]
      field_simp [hc]
      ring

theorem actual_Hartree_moment_locked_scale_profile_time_hasDerivAt
    {c : ℝ → ℝ} {s cs r : ℝ} (hc : HasDerivAt c cs s) (hr : 0 < r) :
    HasDerivAt
      (fun t => actualMomentLockedScaleProfile (c t) r)
      (cs * actualMomentLockedScaleProfileParameterTangent (c s) r) s := by
  convert
    (actual_Hartree_moment_locked_scale_profile_parameter_hasDerivAt
      (c s) r hr).comp s hc using 1
  · rfl
  · ring

theorem actual_Hartree_moment_locked_phase_source_time_hasDerivAt
    {c : ℝ → ℝ} {s cs r : ℝ} (hc : HasDerivAt c cs s) :
    HasDerivAt
      (fun t => actualMomentLockedPhaseSource (c t) r)
      (((cs * actualMomentLockedAmplitudeTangent (c s) r : ℝ) : ℂ)) s := by
  have h := (monopoleMovingCutoffTime_hasDerivAt hc r).ofReal_comp
  simpa only [actualMomentLockedPhaseSource, actualMomentLockedCore,
    actualMomentLockedAmplitudeTangent, mul_assoc] using h

theorem actual_Hartree_moment_locked_scale_source_time_hasDerivAt
    {c : ℝ → ℝ} {s cs r : ℝ} (hc : HasDerivAt c cs s) (hr : 0 < r) :
    HasDerivAt
      (fun t => actualMomentLockedScaleSource (c t) r)
      (Complex.I *
        ((cs * actualMomentLockedScaleProfileParameterTangent (c s) r : ℝ) : ℂ)) s := by
  have h :=
    (actual_Hartree_moment_locked_scale_profile_time_hasDerivAt hc hr).ofReal_comp
  simpa only [actualMomentLockedScaleSource] using h.const_mul Complex.I

theorem actual_Hartree_moment_locked_scaled_phase_source_c_time_hasDerivAt
    (a : ℝ) {c : ℝ → ℝ} {s cs r : ℝ} (hc : HasDerivAt c cs s) :
    HasDerivAt
      (fun t => actualMomentLockedScaledPhaseSource a (c t) r)
      ((((a ^ 2 : ℝ) : ℂ)) *
        (((cs * actualMomentLockedAmplitudeTangent (c s) (a * r) : ℝ) : ℂ))) s := by
  have h :=
    actual_Hartree_moment_locked_phase_source_time_hasDerivAt
      (c := c) (s := s) (cs := cs) (r := a * r) hc
  simpa only [actualMomentLockedScaledPhaseSource] using
    h.const_mul (((a ^ 2 : ℝ) : ℂ))

theorem actual_Hartree_moment_locked_scaled_scale_source_c_time_hasDerivAt
    (a : ℝ) {c : ℝ → ℝ} {s cs r : ℝ}
    (hc : HasDerivAt c cs s) (har : 0 < a * r) :
    HasDerivAt
      (fun t => actualMomentLockedScaledScaleSource a (c t) r)
      ((((a ^ 2 : ℝ) : ℂ)) * Complex.I *
        ((cs * actualMomentLockedScaleProfileParameterTangent
          (c s) (a * r) : ℝ) : ℂ)) s := by
  have h :=
    actual_Hartree_moment_locked_scale_source_time_hasDerivAt
      (c := c) (s := s) (cs := cs) (r := a * r) hc har
  simpa only [actualMomentLockedScaledScaleSource, mul_assoc] using
    h.const_mul (((a ^ 2 : ℝ) : ℂ))

end HBL.TypeIIDynamicSelection
