import HBL.AffineTailPlusBoundaryLimit

/-!
One-dimensional local differential identities needed for the real Hartree
zero-mode calculation.  These are verified with the concrete potential
V(r)=3/(1+r^2)^2 and the already certified imaginary-channel zero mode.
No property of the nonlocal operator is assumed here.
-/

noncomputable section

open scoped Topology ContDiff

namespace HBL.Modulation.AffineTail

/-- Explicit derivative of the conjugated Hartree potential. -/
def potentialDerivative (r : ℝ) : ℝ :=
  -12 * r / (1 + r ^ 2) ^ 3

theorem potential_hasDerivAt (r : ℝ) :
    HasDerivAt potential (potentialDerivative r) r := by
  have hA : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    have h := (hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).pow 2)
    convert h using 1
    · funext x
      simp
    · norm_num
  have hApos : 0 < (1 + r ^ 2 : ℝ) := by positivity
  have hAne : (1 + r ^ 2 : ℝ) ≠ 0 := ne_of_gt hApos
  have hinv := (hA.pow 2).inv (pow_ne_zero 2 hAne)
  have h := hinv.const_mul (3 : ℝ)
  change HasDerivAt (fun x : ℝ => 3 * ((1 + x ^ 2) ^ 2)⁻¹)
    (3 * (-(2 * (1 + r ^ 2) ^ (2 - 1) * (2 * r)) *
       (((1 + r ^ 2) ^ 2) ^ 2)⁻¹)) r at h
  convert h using 1
  · funext x
    simp only [potential, div_eq_mul_inv]
  · unfold potentialDerivative
    simp only [Nat.reduceSubDiff, pow_one]
    field_simp [hAne]
    ring

theorem potential_deriv_eq (r : ℝ) :
    deriv potential r = potentialDerivative r :=
  (potential_hasDerivAt r).deriv

/-- Algebraic zero-mode equation in the H-minus channel. -/
theorem resonanceMinus_second_eq_potential (r : ℝ) :
    deriv (deriv resonanceMinus) r =
      -potential r * resonanceMinus r := by
  have hzero := hMinus_resonanceMinus_zero r
  unfold hMinusApply at hzero
  linarith

/-- First derivative of the scaling resonance, with no second derivative. -/
theorem resonancePlus_deriv_from_minus (r : ℝ) :
    deriv resonancePlus r =
      deriv resonanceMinus r / 2 -
        r * potential r * resonanceMinus r := by
  rw [resonancePlus_deriv_eq, resonanceMinus_second_eq_potential]
  ring

end HBL.Modulation.AffineTail
