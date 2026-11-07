import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedProjection
import HBL.MonopoleMovingCutoffSpatial
import HBL.MonopoleMovingCutoffTime
import Mathlib.Tactic

/-!
# Joint amplitude/spatial tangent of the true moment-locked core

The scaled Kummer speed sources depend both on the moment-locked amplitude
c(s) and on the moving physical argument a(s) r.  This file differentiates
the genuine two-variable path before applying the outer a(s)^2 prefactor.

The c=0 case is handled by the actual cutoff plateau and not by
differentiating |c| at zero.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualMomentLockedCoreSpatialTangent (c r : ℝ) : ℝ :=
  deriv bubble r +
    c * ((1 - cutoff (|c| * r / 4)) *
      deriv monopoleRadialProfile r -
      (|c| / 4) * deriv cutoff (|c| * r / 4) *
        monopoleRadialProfile r)

def actualMomentLockedCoreTotalTangent
    (c r cdot rdot : ℝ) : ℝ :=
  cdot * actualMomentLockedAmplitudeTangent c r +
    rdot * actualMomentLockedCoreSpatialTangent c r

theorem actual_Hartree_moment_locked_core_joint_hasDerivAt
    (c x : ℝ → ℝ) {s cdot xdot : ℝ}
    (hc : HasDerivAt c cdot s)
    (hx : HasDerivAt x xdot s)
    (hxpos : 0 < x s) :
    HasDerivAt
      (fun t => actualMomentLockedCore (c t) (x t))
      (actualMomentLockedCoreTotalTangent (c s) (x s) cdot xdot) s := by
  have hBubble :=
    (bubble_differentiable (x s)).hasDerivAt.comp s hx
  have hP : HasDerivAt
      (monopoleRadialProfile ∘ x)
      (deriv monopoleRadialProfile (x s) * xdot) s := by
    exact
      (monopoleRadialProfile_hasDerivAt hxpos).differentiableAt.hasDerivAt.comp
        s hx
  by_cases hc0 : c s = 0
  · have hargCont :
        ContinuousAt (fun t => |c t| * x t / 4) s := by
      exact ((hc.continuousAt.abs.mul hx.continuousAt).div_const 4)
    have hz : |c s| * x s / 4 < 1 := by
      rw [hc0, abs_zero, zero_mul, zero_div]
      norm_num
    have hev := hargCont.eventually (Iio_mem_nhds hz)
    have hProd := hc.mul hP
    have hModel :=
      hBubble.add hProd
    have hTarget :
        actualMomentLockedCoreTotalTangent (c s) (x s) cdot xdot =
          deriv bubble (x s) * xdot +
            (cdot * monopoleRadialProfile (x s) +
              c s * (deriv monopoleRadialProfile (x s) * xdot)) := by
      rw [hc0]
      unfold actualMomentLockedCoreTotalTangent
        actualMomentLockedAmplitudeTangent actualMomentLockedCoreSpatialTangent
      have hcut0 : cutoff 0 = 0 :=
        cutoff_zero_of_le_one 0 (by norm_num)
      simp only [abs_zero, zero_mul, zero_div, hcut0, sub_zero, one_mul]
      ring
    rw [hTarget]
    apply hModel.congr_of_eventuallyEq
    filter_upwards [hev] with t ht
    unfold actualMomentLockedCore
    rw [monopoleMovingCutoffProfile_eq,
      cutoff_zero_of_le_one _ ht.le]
    simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, sub_zero,
      mul_one]
  · have habs0 : HasDerivAt (fun a : ℝ => |a|) (|c s| / c s) (c s) := by
      rcases lt_or_gt_of_ne hc0 with hn | hp
      · have hneg : HasDerivAt (fun a : ℝ => |a|) (-1) (c s) := by
          apply (hasDerivAt_neg (c s)).congr_of_eventuallyEq
          filter_upwards [Iio_mem_nhds hn] with a ha
          exact abs_of_neg ha
        convert hneg using 1
        rw [abs_of_neg hn]
        field_simp [hc0]
      · have hpos : HasDerivAt (fun a : ℝ => |a|) 1 (c s) := by
          apply (hasDerivAt_id (c s)).congr_of_eventuallyEq
          filter_upwards [Ioi_mem_nhds hp] with a ha
          exact abs_of_pos ha
        convert hpos using 1
        rw [abs_of_pos hp, div_self hc0]
    have habs := habs0.comp s hc
    have harg := (habs.mul hx).div_const 4
    have hcut :=
      ((contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).1
        (|c s| * x s / 4)).hasDerivAt.comp s harg
    have heta := (hasDerivAt_const s (1 : ℝ)).sub hcut
    have hProd := (hc.mul heta).mul hP
    have hModel := hBubble.add hProd
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply] at hModel
    convert hModel using 1
    · funext t
      unfold actualMomentLockedCore
      rw [monopoleMovingCutoffProfile_eq]
      rfl
    · unfold actualMomentLockedCoreTotalTangent
        actualMomentLockedAmplitudeTangent actualMomentLockedCoreSpatialTangent
      field_simp [hc0]
      ring_nf

/-- Full time derivative of the genuine scaled PHASE direction, including
a(s)^2, the amplitude motion c_s, and the moving argument a(s) r. -/
theorem actual_Hartree_moment_locked_scaled_phase_source_time_hasDerivAt
    (a c : ℝ → ℝ) {s adot cdot r : ℝ}
    (ha : HasDerivAt a adot s)
    (hc : HasDerivAt c cdot s)
    (har : 0 < a s * r) :
    HasDerivAt
      (fun t => actualMomentLockedScaledPhaseSource (a t) (c t) r)
      (((2 * a s * adot : ℝ) : ℂ) *
          actualMomentLockedPhaseSource (c s) (a s * r) +
        ((((a s) ^ 2 : ℝ) : ℂ)) *
          ((actualMomentLockedCoreTotalTangent
            (c s) (a s * r) cdot (adot * r) : ℝ) : ℂ)) s := by
  have hx : HasDerivAt (fun t => a t * r) (adot * r) s :=
    ha.mul_const r
  have hCore :=
    actual_Hartree_moment_locked_core_joint_hasDerivAt
      c (fun t => a t * r) hc hx har
  have ha2Real : HasDerivAt (fun t => a t ^ 2) (2 * a s * adot) s := by
    convert ha.mul ha using 1
    · funext t
      simp only [Pi.mul_apply, pow_two]
    · ring
  have hReal := ha2Real.mul hCore
  have h := hReal.ofReal_comp
  convert h using 1
  · funext t
    simp only [actualMomentLockedScaledPhaseSource,
      actualMomentLockedPhaseSource, Pi.mul_apply]
    push_cast
    rfl
  · simp only [actualMomentLockedPhaseSource]
    push_cast
    ring

end HBL.TypeIIDynamicSelection
