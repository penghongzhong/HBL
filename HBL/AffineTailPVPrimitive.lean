import HBL.AffineTailSecondRationalIntegral

/-!
Derivative and symmetric-cutoff cancellation for the remaining Cauchy
principal-value term in the radial Hartree affine charge.

The primitive and its endpoint cancellation are established explicitly;
the full improper-integral exchange remains a separate analytic task.
-/

noncomputable section

open Filter
open scoped Topology

namespace HBL.Modulation.AffineTail

/-- Primitive of the simple Cauchy kernel off its two singular radii. -/
def pvRationalPrimitive (r rho : ℝ) : ℝ :=
  (Real.log (r + rho) - Real.log (r - rho)) / (2 * r)

theorem pvRationalPrimitive_hasDerivAt (r rho : ℝ)
    (hr : r ≠ 0) (hp : r + rho ≠ 0) (hm : r - rho ≠ 0) :
    HasDerivAt (pvRationalPrimitive r)
      ((r ^ 2 - rho ^ 2)⁻¹) rho := by
  have hsep : r ^ 2 - rho ^ 2 ≠ 0 := by
    intro hz
    have h : (r + rho) * (r - rho) = 0 := by nlinarith [hz]
    exact (mul_ne_zero hp hm) h
  have hd := (splitRadialLog_hasDerivAt r rho hp hm).div_const (2 * r)
  unfold pvRationalPrimitive
  convert hd using 1 <;>
    simp only [Pi.sub_apply, Pi.div_apply] <;>
    (first | rfl | (field_simp [hr, hsep] <;> ring))

@[simp]
theorem pvRationalPrimitive_at_zero (r : ℝ) :
    pvRationalPrimitive r 0 = 0 := by
  simp [pvRationalPrimitive]

/-- Algebraic cancellation of the two singular logarithms at r-e and r+e. -/
theorem symmetricPV_gap_eq (r e : ℝ) :
    pvRationalPrimitive r (r - e) -
        pvRationalPrimitive r (r + e) =
      (Real.log (2 * r - e) - Real.log (2 * r + e)) / (2 * r) := by
  have h1 : r + (r - e) = 2 * r - e := by ring
  have h2 : r - (r - e) = e := by ring
  have h3 : r + (r + e) = 2 * r + e := by ring
  have h4 : r - (r + e) = -e := by ring
  simp only [pvRationalPrimitive, h1, h2, h3, h4, Real.log_neg_eq_log]
  ring

/-- The symmetric logarithmic boundary gap tends to zero. -/
theorem symmetricPV_log_gap_tendsto_zero (r : ℝ) (hr : 0 < r) :
    Tendsto
      (fun e : ℝ => Real.log (2 * r - e) - Real.log (2 * r + e))
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hn : (2 * r : ℝ) ≠ 0 := by positivity
  have hl : ContinuousAt (fun e : ℝ => 2 * r - e) 0 := by fun_prop
  have hu : ContinuousAt (fun e : ℝ => 2 * r + e) 0 := by fun_prop
  have hll := (Real.continuousAt_log hn).comp (0 : ℝ) hl
  have hru := (Real.continuousAt_log hn).comp (0 : ℝ) hu
  have h := hll.tendsto.sub hru.tendsto
  simpa using h

/-- The symmetric principal-value cutoff has no surviving pole boundary. -/
theorem symmetricPV_primitive_gap_tendsto_zero (r : ℝ) (hr : 0 < r) :
    Tendsto
      (fun e : ℝ =>
        pvRationalPrimitive r (r - e) -
          pvRationalPrimitive r (r + e))
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hlim :
      Tendsto
        (fun e : ℝ =>
          (Real.log (2 * r - e) - Real.log (2 * r + e)) / (2 * r))
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_div] using
      (symmetricPV_log_gap_tendsto_zero r hr).div_const (2 * r)
  apply hlim.congr'
  exact Filter.Eventually.of_forall
    (fun e : ℝ => (symmetricPV_gap_eq r e).symm)

end HBL.Modulation.AffineTail
