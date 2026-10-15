import HBL.RadialDotH1Model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Exact change-of-variables identity for the manuscript threshold test.

The manuscript tests
  ell_zeta(f) = integral zeta(y) * y * f(y) dy.
For logarithmic scale a, the pullback is
  T_a f(y) = exp(-a/2) f(exp(-a)y).
After y = exp(a) r the moved kernel is exactly
  exp(3a/2) zeta(exp(a)r) r,
which is HBL's transportedRadialTest.

This module proves the identity with the naturally transformed upper
endpoint.  A later compact-support lemma replaces that moving endpoint
by the fixed finite radius used in the Hilbert model.
-/

noncomputable section

open MeasureTheory
open scoped Topology ContDiff

namespace HBL.Modulation

/-- Pointwise identity behind the logarithmic-scale change of variables. -/
theorem transportedRadialTest_scaled_pullback_integrand
    (zeta f : ℝ → ℝ) (a r : ℝ) :
    Real.exp a *
      (zeta (Real.exp a * r) *
        radialU (scalePullback f a) (Real.exp a * r)) =
      transportedRadialTest zeta a r * f r := by
  have harg :
      Real.exp (-a) * (Real.exp a * r) = r := by
    calc
      Real.exp (-a) * (Real.exp a * r) =
          (Real.exp (-a) * Real.exp a) * r := by ring
      _ = r := by
        rw [← Real.exp_add]
        simp
  have hcoef :
      Real.exp a * Real.exp a * Real.exp (-a / 2) =
        Real.exp ((3 / 2 : ℝ) * a) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [radialU, scalePullback, transportedRadialTest]
  rw [harg]
  calc
    Real.exp a *
        (zeta (Real.exp a * r) *
          (Real.exp a * r * (Real.exp (-a / 2) * f r))) =
      (Real.exp a * Real.exp a * Real.exp (-a / 2)) *
        zeta (Real.exp a * r) * r * f r := by ring
    _ = Real.exp ((3 / 2 : ℝ) * a) *
        zeta (Real.exp a * r) * r * f r := by rw [hcoef]
    _ = (Real.exp ((3 / 2 : ℝ) * a) *
        zeta (Real.exp a * r) * r) * f r := by ring

/-- Exact finite-interval change of variables. The upper endpoint moves
by exp(-a); no compact-support assumption is used in this identity. -/
theorem transportedRadialTestIntegral_dynamic_eq_scalePullback
    (R : ℝ) (zeta f : ℝ → ℝ) (a : ℝ) :
    transportedRadialTestIntegral (Real.exp (-a) * R) zeta f a =
      ∫ y in (0 : ℝ)..R,
        zeta y * radialU (scalePullback f a) y := by
  let G : ℝ → ℝ :=
    fun y => zeta y * radialU (scalePullback f a) y
  have hcv :=
    intervalIntegral.smul_integral_comp_mul_left
      G (Real.exp a)
      (a := (0 : ℝ)) (b := Real.exp (-a) * R)
  have hbound :
      Real.exp a * (Real.exp (-a) * R) = R := by
    calc
      Real.exp a * (Real.exp (-a) * R) =
          (Real.exp a * Real.exp (-a)) * R := by ring
      _ = R := by
        rw [← Real.exp_add]
        simp
  have hleft :
      (Real.exp a) •
          (∫ r in (0 : ℝ)..Real.exp (-a) * R,
            G (Real.exp a * r)) =
        transportedRadialTestIntegral
          (Real.exp (-a) * R) zeta f a := by
    rw [← intervalIntegral.integral_smul]
    unfold transportedRadialTestIntegral
    apply intervalIntegral.integral_congr
    intro r _
    change Real.exp a * G (Real.exp a * r) =
      transportedRadialTest zeta a r * f r
    exact transportedRadialTest_scaled_pullback_integrand zeta f a r
  rw [hbound] at hcv
  rw [hleft] at hcv
  exact hcv

end HBL.Modulation
