import HBL.AffineTailPVRegularConstant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
A fully specified finite-interval Cauchy-kernel integral.

The singularity at rho=r is excluded from BOTH pieces. Integrability
is established from continuity away from the poles, not passed as
an unverified hypothesis. The common symmetric-cutoff expression is
then obtained by adding the two independent FTC identities.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- FTC for the rational Cauchy kernel on an arbitrary interval excluding
both real poles. No global integral is invoked. -/
theorem pvKernel_integral_away
    (r a b : ℝ) (hr : r ≠ 0)
    (havoid : ∀ x ∈ Set.uIcc a b,
      r + x ≠ 0 ∧ r - x ≠ 0) :
    (∫ x in a..b, (r ^ 2 - x ^ 2)⁻¹) =
      pvRationalPrimitive r b - pvRationalPrimitive r a := by
  have hden : ∀ x ∈ Set.uIcc a b,
      r ^ 2 - x ^ 2 ≠ 0 := by
    intro x hx hzero
    have hm : (r + x) * (r - x) = 0 := by nlinarith [hzero]
    exact (mul_ne_zero (havoid x hx).1 (havoid x hx).2) hm
  have hcont : ContinuousOn
      (fun x : ℝ => (r ^ 2 - x ^ 2)⁻¹) (Set.uIcc a b) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn.inv₀ hden
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => pvRationalPrimitive_hasDerivAt r x hr
      (havoid x hx).1 (havoid x hx).2)
    hcont.intervalIntegrable

/-- The left interval is strictly separated from the Cauchy pole. -/
theorem pvKernel_integral_left
    (r e : ℝ) (hr : 0 < r) (he : 0 < e) (her : e < r) :
    (∫ x in (0 : ℝ)..(r - e), (r ^ 2 - x ^ 2)⁻¹) =
      pvRationalPrimitive r (r - e) := by
  have h0 : (0 : ℝ) ≤ r - e := by linarith
  have havoid : ∀ x ∈ Set.uIcc (0 : ℝ) (r - e),
      r + x ≠ 0 ∧ r - x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le h0] at hx
    have hlow := hx.1
    have hupp := hx.2
    constructor
    · exact ne_of_gt (show 0 < r + x by linarith)
    · exact ne_of_gt (show 0 < r - x by linarith)
  simpa using pvKernel_integral_away r 0 (r - e) (ne_of_gt hr) havoid

/-- The right interval is strictly separated from the Cauchy pole. -/
theorem pvKernel_integral_right
    (r e R : ℝ) (hr : 0 < r) (he : 0 < e)
    (hR : r + e ≤ R) :
    (∫ x in (r + e)..R, (r ^ 2 - x ^ 2)⁻¹) =
      pvRationalPrimitive r R - pvRationalPrimitive r (r + e) := by
  have havoid : ∀ x ∈ Set.uIcc (r + e) R,
      r + x ≠ 0 ∧ r - x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hR] at hx
    have hlow := hx.1
    constructor
    · exact ne_of_gt (show 0 < r + x by linarith)
    · exact ne_of_lt (show r - x < 0 by linarith)
  exact pvKernel_integral_away r (r + e) R (ne_of_gt hr) havoid

/-- Exact algebraic formula for the symmetric finite-radius truncation. -/
theorem pvKernel_integral_split
    (r e R : ℝ) (hr : 0 < r) (he : 0 < e)
    (her : e < r) (hR : r + e ≤ R) :
    (∫ x in (0 : ℝ)..(r - e), (r ^ 2 - x ^ 2)⁻¹) +
        (∫ x in (r + e)..R, (r ^ 2 - x ^ 2)⁻¹) =
      (pvRationalPrimitive r (r - e) -
        pvRationalPrimitive r (r + e)) +
        pvRationalPrimitive r R := by
  rw [pvKernel_integral_left r e hr he her,
    pvKernel_integral_right r e R hr he hR]
  ring

end HBL.Modulation.AffineTail
