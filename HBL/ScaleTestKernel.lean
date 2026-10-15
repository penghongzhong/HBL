import HBL.ScalePhaseLocalIFT
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Actual scale transport of a compactly supported radial test function for
the first modulation lemma in the manuscript.

If u is pulled back by exp(a), the one-dimensional radial test
`integral zeta(r) * r * u(r) dr` has transported kernel
`exp(3*a/2) * zeta(exp(a)*r) * r`.
Its derivative at a=0 and the corresponding integration-by-parts
identity are proved below.  This is genuinely the manuscript's
radial-conjugated test rather than an arbitrary abstract dual family.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology

namespace HBL.Modulation

/-- The test kernel after moving the scale pullback onto the fixed test. -/
def transportedRadialTest (zeta : ℝ → ℝ) (a r : ℝ) : ℝ :=
  Real.exp ((3 / 2 : ℝ) * a) * zeta (Real.exp a * r) * r

/-- The classical derivative of the transported test kernel. -/
def transportedRadialTestDerivative (zeta : ℝ → ℝ) (a r : ℝ) : ℝ :=
  Real.exp ((3 / 2 : ℝ) * a) *
    ((3 / 2 : ℝ) * zeta (Real.exp a * r) +
      (Real.exp a * r) * deriv zeta (Real.exp a * r)) * r

/-- Differentiability in the logarithmic scale variable at every real radius. -/
theorem transportedRadialTest_hasDerivAt (zeta : ℝ → ℝ)
    (hzeta : ContDiff ℝ 1 zeta) (a r : ℝ) :
    HasDerivAt (fun b : ℝ => transportedRadialTest zeta b r)
      (transportedRadialTestDerivative zeta a r) a := by
  have hcoeff :
      HasDerivAt (fun b : ℝ => Real.exp ((3 / 2 : ℝ) * b))
        ((3 / 2 : ℝ) * Real.exp ((3 / 2 : ℝ) * a)) a := by
    have h := ((hasDerivAt_id a).mul_const (3 / 2 : ℝ)).exp
    simpa only [id_eq, one_mul, mul_comm] using h
  have harg :
      HasDerivAt (fun b : ℝ => Real.exp b * r)
        (Real.exp a * r) a := by
    simpa using (Real.hasDerivAt_exp a).mul_const r
  have hz :
      HasDerivAt (fun b : ℝ => zeta (Real.exp b * r))
        (deriv zeta (Real.exp a * r) * (Real.exp a * r)) a :=
    ((hzeta.differentiable (by norm_num) (Real.exp a * r)).hasDerivAt).comp a harg
  have hcalc := (hcoeff.mul hz).mul_const r
  change HasDerivAt (fun b : ℝ => transportedRadialTest zeta b r) _ a at hcalc
  convert hcalc using 1
  dsimp [transportedRadialTestDerivative]
  ring

/-- At log-scale zero the transported test is the original test kernel. -/
@[simp]
theorem transportedRadialTest_zero (zeta : ℝ → ℝ) (r : ℝ) :
    transportedRadialTest zeta 0 r = r * zeta r := by
  simp [transportedRadialTest, mul_comm]

/-- Exact pointwise scale derivative at log-scale zero. -/
theorem transportedRadialTest_hasDerivAt_zero (zeta : ℝ → ℝ)
    (hzeta : ContDiff ℝ 1 zeta) (r : ℝ) :
    HasDerivAt (fun a : ℝ => transportedRadialTest zeta a r)
      (r * ((3 / 2 : ℝ) * zeta r + r * deriv zeta r)) 0 := by
  convert transportedRadialTest_hasDerivAt zeta hzeta 0 r using 1 <;>
    simp [transportedRadialTestDerivative] <;> ring

/-- The radial integration-by-parts identity responsible for the minus sign
in the scale column of the normalized modulation Jacobian.
The condition zeta(R)=0 is satisfied by a compactly supported test with
support strictly inside (0,R). -/
theorem transportedRadialTest_scale_ibp
    (R : ℝ) (zeta f : ℝ → ℝ)
    (hzeta : ContDiff ℝ 1 zeta) (hf : ContDiff ℝ 1 f)
    (hzetaR : zeta R = 0) :
    (∫ r in (0 : ℝ)..R,
      r * ((3 / 2 : ℝ) * zeta r + r * deriv zeta r) * f r) =
    -(∫ r in (0 : ℝ)..R,
      zeta r * r * (f r / 2 + r * deriv f r)) := by
  let A : ℝ → ℝ :=
    fun r => r * ((3 / 2 : ℝ) * zeta r + r * deriv zeta r) * f r
  let B : ℝ → ℝ :=
    fun r => zeta r * r * (f r / 2 + r * deriv f r)
  let J : ℝ → ℝ := fun r => r ^ 2 * zeta r * f r
  have hza : Continuous (deriv zeta) := hzeta.continuous_deriv_one
  have hfa : Continuous (deriv f) := hf.continuous_deriv_one
  have hA : Continuous A := by
    dsimp [A]
    fun_prop
  have hB : Continuous B := by
    dsimp [B]
    fun_prop
  have hAi := hA.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hBi := hB.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hJ (r : ℝ) : HasDerivAt J (A r + B r) r := by
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
      convert (hasDerivAt_id r).pow 2 using 1
      · funext x
        simp only [Pi.pow_apply, id_eq]
      · norm_num
    have hz : HasDerivAt zeta (deriv zeta r) r :=
      (hzeta.differentiable (by norm_num) r).hasDerivAt
    have hfr : HasDerivAt f (deriv f r) r :=
      (hf.differentiable (by norm_num) r).hasDerivAt
    have hder := (hp.mul hz).mul hfr
    apply hder.congr_deriv
    dsimp [J, A, B]
    ring
  have hzero :
      (∫ r in (0 : ℝ)..R, A r + B r) = 0 := by
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hJ r) (hAi.add hBi)
    simpa [J, hzetaR] using hfund
  rw [intervalIntegral.integral_add hAi hBi] at hzero
  change (∫ r in (0 : ℝ)..R, A r) =
    -(∫ r in (0 : ℝ)..R, B r)
  linarith

/-- Normalization of the compact scale-mode test forces the scale
Jacobian entry -1, with no additional Jacobian hypothesis. -/
theorem transportedRadialTest_scale_normalized
    (R : ℝ) (zeta f : ℝ → ℝ)
    (hzeta : ContDiff ℝ 1 zeta) (hf : ContDiff ℝ 1 f)
    (hzetaR : zeta R = 0)
    (hNorm :
      (∫ r in (0 : ℝ)..R,
        zeta r * r * (f r / 2 + r * deriv f r)) = 1) :
    (∫ r in (0 : ℝ)..R,
      r * ((3 / 2 : ℝ) * zeta r + r * deriv zeta r) * f r) = -1 := by
  simpa [hNorm] using
    transportedRadialTest_scale_ibp R zeta f hzeta hf hzetaR

end HBL.Modulation
