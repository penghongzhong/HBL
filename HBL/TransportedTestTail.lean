import HBL.RadialEnergyHilbertBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
Pointwise logarithmic-scale differentiation of the actual transported
primitive representing the radial threshold test in the L2 energy space.

The tested dual kernel is Q_a(s) = integral_s^R K_a(r) dr, where
K_a(r) = exp(3a/2) * zeta(exp(a)r) * r.

The derivative of Q_a at a=0 is the tail integral of the previously
verified kernel derivative. This proves the pointwise differentiation
needed for the C1 estimate in the L2 operator norm. It is NOT yet the
norm-C1 conclusion itself.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology

namespace HBL.Modulation

/-- Exact transported primitive of the radial orthogonality test. -/
def transportedTestTail (R : ℝ) (zeta : ℝ → ℝ) (a s : ℝ) : ℝ :=
  ∫ r in s..R, transportedRadialTest zeta a r

/-- Classical transported primitive at logarithmic scale zero. -/
theorem transportedTestTail_zero
    (R : ℝ) (zeta : ℝ → ℝ) (s : ℝ) :
    transportedTestTail R zeta 0 s =
      ∫ r in s..R, r * zeta r := by
  apply intervalIntegral.integral_congr
  intro r _
  exact transportedRadialTest_zero zeta r

/-- The derivative of the transported primitive is the tail integral
of the scale derivative of the compact test kernel. -/
theorem transportedTestTail_hasDerivAt_zero
    (R s : ℝ) (hR : 0 ≤ R) (hs : 0 ≤ s)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    HasDerivAt (fun a : ℝ => transportedTestTail R zeta a s)
      (∫ r in s..R, transportedRadialTestDerivative zeta 0 r) 0 := by
  have hRderiv :
      HasDerivAt
        (fun a : ℝ => ∫ r in (0 : ℝ)..R, transportedRadialTest zeta a r)
        (∫ r in (0 : ℝ)..R, transportedRadialTestDerivative zeta 0 r) 0 := by
    have hd := transportedRadialTestIntegral_hasDerivAt R hR
      zeta (fun _ : ℝ => (1 : ℝ)) hzeta contDiff_const
    change HasDerivAt
      (fun a : ℝ => ∫ r in (0 : ℝ)..R, transportedRadialTest zeta a r * (1 : ℝ))
      (∫ r in (0 : ℝ)..R, transportedRadialTestDerivative zeta 0 r * (1 : ℝ))
      0 at hd
    simpa only [mul_one] using hd
  have hsderiv :
      HasDerivAt
        (fun a : ℝ => ∫ r in (0 : ℝ)..s, transportedRadialTest zeta a r)
        (∫ r in (0 : ℝ)..s, transportedRadialTestDerivative zeta 0 r) 0 := by
    have hd := transportedRadialTestIntegral_hasDerivAt s hs
      zeta (fun _ : ℝ => (1 : ℝ)) hzeta contDiff_const
    change HasDerivAt
      (fun a : ℝ => ∫ r in (0 : ℝ)..s, transportedRadialTest zeta a r * (1 : ℝ))
      (∫ r in (0 : ℝ)..s, transportedRadialTestDerivative zeta 0 r * (1 : ℝ))
      0 at hd
    simpa only [mul_one] using hd
  have hd := hRderiv.sub hsderiv
  have hEq (a : ℝ) :
      transportedTestTail R zeta a s =
        (∫ r in (0 : ℝ)..R, transportedRadialTest zeta a r) -
          ∫ r in (0 : ℝ)..s, transportedRadialTest zeta a r := by
    have hc : Continuous (fun r : ℝ => transportedRadialTest zeta a r) := by
      dsimp [transportedRadialTest]
      have hz : Continuous zeta := hzeta.continuous
      fun_prop
    exact (intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable (μ := volume) (a := 0) (b := R))
      (hc.intervalIntegrable (μ := volume) (a := 0) (b := s))).symm
  have hD :
      (∫ r in s..R, transportedRadialTestDerivative zeta 0 r) =
        (∫ r in (0 : ℝ)..R, transportedRadialTestDerivative zeta 0 r) -
          ∫ r in (0 : ℝ)..s, transportedRadialTestDerivative zeta 0 r := by
    have hc : Continuous (transportedRadialTestDerivative zeta 0) := by
      have hz : Continuous zeta := hzeta.continuous
      have hdz : Continuous (deriv zeta) := hzeta.continuous_deriv_one
      change Continuous (fun r : ℝ =>
        Real.exp ((3 / 2 : ℝ) * 0) *
          ((3 / 2 : ℝ) * zeta (Real.exp 0 * r) +
            (Real.exp 0 * r) * deriv zeta (Real.exp 0 * r)) * r)
      fun_prop
    exact (intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable (μ := volume) (a := 0) (b := R))
      (hc.intervalIntegrable (μ := volume) (a := 0) (b := s))).symm
  convert hd using 1
  · funext a
    exact hEq a

end HBL.Modulation
