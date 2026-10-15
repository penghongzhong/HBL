import HBL.RadialEnergyCompletion
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

/-!
Radial energy representation of compact test functionals.

The manuscript uses l_zeta(f) = ∫ zeta(r) (r f(r)) dr.
The radial energy coordinate is q = (r f)'.
Set Q_zeta(s) = ∫_s^R zeta(r) dr. Then integration by parts gives

    ∫_0^R zeta(r) r f(r) dr
       = ∫_0^R Q_zeta(s) (r f(r))'|_{r=s} ds.

This exactly transfers the orthogonality test from the radial profile to
the half-line Dirichlet energy coordinate. It does not require f(R)=0.
The next module will use Cauchy-Schwarz to obtain the operator norm bound.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology

namespace HBL.Modulation

/-- Primitive of a compact test, integrated backward from the cutoff R. -/
def testTailPrimitive (R : ℝ) (zeta : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in s..R, zeta t

/-- Exact derivative of the test primitive. -/
theorem testTailPrimitive_hasDerivAt
    (R : ℝ) (zeta : ℝ → ℝ) (hzeta : Continuous zeta) (s : ℝ) :
    HasDerivAt (testTailPrimitive R zeta) (-zeta s) s := by
  have hInt : IntervalIntegrable zeta volume s R :=
    hzeta.intervalIntegrable s R
  have hMeas : StronglyMeasurableAtFilter zeta (𝓝 s) :=
    hzeta.aestronglyMeasurable.stronglyMeasurableAtFilter
  exact intervalIntegral.integral_hasDerivAt_left hInt hMeas hzeta.continuousAt

/-- The cutoff boundary term vanishes at R. -/
@[simp]
theorem testTailPrimitive_right (R : ℝ) (zeta : ℝ → ℝ) :
    testTailPrimitive R zeta R = 0 := by
  simp [testTailPrimitive]

/-- Differentiability and continuous derivative of the test primitive.
This is its actual C1 regularity, not a hypothetical dual-space premise. -/
theorem testTailPrimitive_contDiff_one (R : ℝ) (zeta : ℝ → ℝ)
    (hzeta : Continuous zeta) :
    ContDiff ℝ 1 (testTailPrimitive R zeta) := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · intro s
    exact (testTailPrimitive_hasDerivAt R zeta hzeta s).differentiableAt
  · have hderiv :
        deriv (testTailPrimitive R zeta) = fun s => -zeta s := by
      funext s
      exact (testTailPrimitive_hasDerivAt R zeta hzeta s).deriv
    rw [hderiv]
    exact hzeta.neg

/-- The exact Green-type identity transferring the actual test to the
radial homogeneous energy coordinate q=(r f)'.
No outer Dirichlet condition on f is needed. -/
theorem compactTest_energy_coordinate_identity
    (R : ℝ) (zeta f : ℝ → ℝ)
    (hzeta : Continuous zeta) (hf : ContDiff ℝ 1 f) :
    (∫ r in (0 : ℝ)..R, zeta r * radialU f r) =
      ∫ r in (0 : ℝ)..R,
        testTailPrimitive R zeta r * deriv (radialU f) r := by
  let Q : ℝ → ℝ := testTailPrimitive R zeta
  let U : ℝ → ℝ := radialU f
  let A : ℝ → ℝ := fun r => zeta r * U r
  let B : ℝ → ℝ := fun r => Q r * deriv U r
  let J : ℝ → ℝ := fun r => Q r * U r
  have hU : ContDiff ℝ 1 U := radialU_contDiff_one f hf
  have hQ : ContDiff ℝ 1 Q :=
    testTailPrimitive_contDiff_one R zeta hzeta
  have hUc : Continuous (deriv U) := hU.continuous_deriv_one
  have hA : Continuous A := by
    dsimp [A]
    exact hzeta.mul hU.continuous
  have hB : Continuous B := by
    dsimp [B]
    exact hQ.continuous.mul hUc
  have hAi : IntervalIntegrable A volume 0 R := hA.intervalIntegrable 0 R
  have hBi : IntervalIntegrable B volume 0 R := hB.intervalIntegrable 0 R
  have hJ (r : ℝ) : HasDerivAt J (B r - A r) r := by
    have hp : HasDerivAt Q (-zeta r) r :=
      testTailPrimitive_hasDerivAt R zeta hzeta r
    have hu : HasDerivAt U (deriv U r) r :=
      (hU.differentiable (by norm_num) r).hasDerivAt
    have h := hp.mul hu
    apply h.congr_deriv
    dsimp [J, A, B]
    ring
  have hzero :
      (∫ r in (0 : ℝ)..R, B r - A r) = 0 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hJ r) (hBi.sub hAi)
    have hR : J R = 0 := by
      simp [J, Q]
    have h0 : J 0 = 0 := by
      simp [J, U, radialU]
    simpa only [hR, h0, sub_zero, zero_sub, neg_zero] using hFTC
  rw [intervalIntegral.integral_sub hBi hAi] at hzero
  change (∫ r in (0 : ℝ)..R, A r) =
    (∫ r in (0 : ℝ)..R, B r)
  linarith

end HBL.Modulation
