import HBL.AffineTailPVWeightedPrimitive
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
Compact-interval absolute integrability of the translated logarithms
that occur in the radial Hartree kernel. The logarithmic singularity is
locally integrable even when the interval crosses its location.

The result uses Mathlib's unconditional interval integrability of
the real logarithm and its translation rules.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- Translating a logarithmic singularity preserves integrability on
every finite interval, including those containing the singular point. -/
theorem translatedLog_intervalIntegrable (a b c : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log (x - c)) volume a b := by
  have h : IntervalIntegrable Real.log volume (a - c) (b - c) :=
    intervalIntegral.intervalIntegrable_log'
  simpa only [sub_add_cancel] using h.comp_sub_right c

/-- The other sign of a translated logarithm is also interval integrable. -/
theorem reflectedLog_intervalIntegrable (a b c : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log (c - x)) volume a b := by
  have heq :
      (fun x : ℝ => Real.log (c - x)) =
        (fun x : ℝ => Real.log (x - c)) := by
    funext x
    rw [show c - x = -(x - c) by ring, Real.log_neg_eq_log]
  rw [heq]
  exact translatedLog_intervalIntegrable a b c

/-- A constant translation inside a logarithm does not change local L1. -/
theorem shiftedLog_intervalIntegrable (a b c : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log (c + x)) volume a b := by
  have h : IntervalIntegrable Real.log volume (a + c) (b + c) :=
    intervalIntegral.intervalIntegrable_log'
  have hh : IntervalIntegrable
      (fun x : ℝ => Real.log (x + c)) volume a b := by
    simpa only [add_sub_cancel_right] using h.comp_add_right c
  have heq :
      (fun x : ℝ => Real.log (c + x)) =
        (fun x : ℝ => Real.log (x + c)) := by
    funext x
    rw [add_comm c x]
  rw [heq]
  exact hh

/-- The two logarithms from the radial kernel have integrable difference
on every finite interval, even across the diagonal. -/
theorem splitRadialLog_intervalIntegrable (r a b : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => Real.log (r + x) - Real.log (r - x))
      volume a b :=
  (shiftedLog_intervalIntegrable a b r).sub
    (reflectedLog_intervalIntegrable a b r)

/-- Multiplying by the smooth rational Hartree source density
preserves finite-interval integrability. -/
theorem splitAffineLogDensity_intervalIntegrable (r a b : ℝ) :
    IntervalIntegrable
      (fun x : ℝ =>
        (Real.log (r + x) - Real.log (r - x)) *
          (x * (1 - x ^ 2) / (2 * (1 + x ^ 2) ^ 3)))
      volume a b := by
  have hc : Continuous
      (fun x : ℝ => x * (1 - x ^ 2) / (2 * (1 + x ^ 2) ^ 3)) := by
    fun_prop (discharger := intro; positivity)
  exact (splitRadialLog_intervalIntegrable r a b).mul_continuousOn
    hc.continuousOn

end HBL.Modulation.AffineTail
