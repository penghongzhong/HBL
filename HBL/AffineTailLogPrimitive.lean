import HBL.AffineTailPVAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
Explicit antiderivative and local calculus for the logarithmic radial
kernel, preparatory to its split-interval integration by parts.
These statements contain no principal-value claims.
-/

noncomputable section

open Filter
open scoped Topology

namespace HBL.Modulation.AffineTail

/-- Rational primitive for the radial scaling-density integrand. -/
def radialLogPrimitive (rho : ℝ) : ℝ :=
  rho ^ 2 / (4 * (1 + rho ^ 2) ^ 2)

/-- An exact derivative; the integrand has no singularity. -/
theorem radialLogPrimitive_hasDerivAt (rho : ℝ) :
    HasDerivAt radialLogPrimitive
      (rho * (1 - rho ^ 2) / (2 * (1 + rho ^ 2) ^ 3)) rho := by
  have hA : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * rho) rho := by
    have h := (hasDerivAt_const rho (1 : ℝ)).add ((hasDerivAt_id rho).pow 2)
    convert h using 1
    · funext x
      simp
    · norm_num
  have hAne : (1 + rho ^ 2 : ℝ) ≠ 0 := by positivity
  have hInv := (hA.pow 2).inv (pow_ne_zero 2 hAne)
  have h := ((hasDerivAt_id rho).pow 2).mul hInv
  have hdiv := h.div_const (4 : ℝ)
  have hfun : radialLogPrimitive =
      (fun x : ℝ => (x ^ 2 * ((1 + x ^ 2) ^ 2)⁻¹) / 4) := by
    funext x
    unfold radialLogPrimitive
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hfun]
  convert hdiv using 1
  · field_simp [hAne]
    ring

/-- The boundary error epsilon * log(epsilon) vanishes at zero. -/
theorem logBoundary_tendsto_zero :
    Tendsto (fun epsilon : ℝ => epsilon * Real.log epsilon)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have h := Real.continuous_mul_log.continuousAt (x := (0 : ℝ))
  simpa only [Real.log_zero, mul_zero] using h.tendsto

/-- Derivative of the nonsingular split logarithm; the integral kernel
is obtained by restricting to one side of rho=r and applying log_div. -/
theorem splitRadialLog_hasDerivAt (r rho : ℝ)
    (hp : r + rho ≠ 0) (hm : r - rho ≠ 0) :
    HasDerivAt
      (fun x : ℝ => Real.log (r + x) - Real.log (r - x))
      (2 * r / (r ^ 2 - rho ^ 2)) rho := by
  have hplus := ((hasDerivAt_const rho r).add (hasDerivAt_id rho)).log hp
  have hminus := ((hasDerivAt_const rho r).sub (hasDerivAt_id rho)).log hm
  have h := hplus.sub hminus
  have hden : r ^ 2 - rho ^ 2 ≠ 0 := by
    intro hz
    have hz' : (r + rho) * (r - rho) = 0 := by nlinarith [hz]
    exact (mul_ne_zero hp hm) hz'
  convert h using 1
  · funext x
    simp
  · field_simp [hp, hm, hden]
    ring

end HBL.Modulation.AffineTail
