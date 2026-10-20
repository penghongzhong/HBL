import HBL.WeightedVolterraOperator
import HBL.WeightedGreenSineModes
import HBL.WeightedHartreeSineOrthogonal

/-!
Actual singular modes of the weighted Volterra operator.

The proved factorization `V V* = G` transfers the actual orthonormal sine
family to the input space.  Orthogonality and Bessel's inequality use only
the actual Green action and the already proved orthonormality of the output
modes.  Neither completeness of the output family nor injectivity of `V`
is needed; no assertion that the transferred family is complete is made.
-/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The positive reciprocal singular-value scale at positive frequency
`n + 1`. -/
def weightedVolterraSineScale (n : ℕ) : ℝ :=
  Real.sqrt (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1)

/-- The actual transferred input mode, formed with the actual Hilbert
adjoint of the Volterra kernel operator. -/
def weightedVolterraSineMode (n : ℕ) : RealL2 halfLineMeasure :=
  weightedVolterraSineScale n •
    ContinuousLinearMap.adjoint weightedVolterraOperator
      (weightedHartreeOrthonormalSineMode n)

private theorem sineDenominator_pos (n : ℕ) :
    0 < 4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1 := by
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith

private theorem sineScale_pos (n : ℕ) :
    0 < weightedVolterraSineScale n :=
  Real.sqrt_pos.mpr (sineDenominator_pos n)

private theorem sineScale_sq (n : ℕ) :
    weightedVolterraSineScale n ^ 2 =
      4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1 :=
  Real.sq_sqrt (sineDenominator_pos n).le

private theorem green_orthonormalSineMode (n : ℕ) :
    weightedFreeGreenOperator (weightedHartreeOrthonormalSineMode n) =
      (1 / (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1)) •
        weightedHartreeOrthonormalSineMode n := by
  unfold weightedHartreeOrthonormalSineMode
  rw [map_smul, weightedFreeGreenOperator_sineMode (n + 1) (Nat.succ_pos n),
    smul_smul, smul_smul]
  congr 1
  ring

private theorem volterra_comp_adjoint_apply (f : RealL2 halfLineMeasure) :
    weightedVolterraOperator
        (ContinuousLinearMap.adjoint weightedVolterraOperator f) =
      weightedFreeGreenOperator f := by
  exact congrArg
    (fun T : RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure => T f)
    weightedVolterraOperator_comp_adjoint

/-- The transferred actual Volterra modes are orthonormal.  Only the
factorization and the individual Green eigenvector identities are used. -/
theorem weightedVolterraSineMode_orthonormal :
    Orthonormal ℝ weightedVolterraSineMode := by
  rw [orthonormal_iff_ite]
  intro n m
  unfold weightedVolterraSineMode
  rw [real_inner_smul_left, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left, volterra_comp_adjoint_apply,
    green_orthonormalSineMode, real_inner_smul_right,
    (orthonormal_iff_ite.mp weightedHartreeOrthonormalSineMode_orthonormal) n m]
  by_cases hnm : n = m
  · subst m
    rw [← sineScale_sq n]
    field_simp [(sineScale_pos n).ne']
  · simp only [ite_eq_right hnm, mul_zero]

/-- The actual Volterra operator sends the transferred mode to the
corresponding output sine mode with its explicit singular value. -/
theorem weightedVolterraOperator_sineMode (n : ℕ) :
    weightedVolterraOperator (weightedVolterraSineMode n) =
      (weightedVolterraSineScale n)⁻¹ • weightedHartreeOrthonormalSineMode n := by
  unfold weightedVolterraSineMode
  rw [map_smul, volterra_comp_adjoint_apply,
    green_orthonormalSineMode, smul_smul]
  congr 1
  rw [← sineScale_sq n]
  field_simp [(sineScale_pos n).ne']

/-- The other actual singular-vector identity uses the same positive
normalization and the actual Hilbert adjoint. -/
theorem weightedVolterraOperator_adjoint_sineMode (n : ℕ) :
    ContinuousLinearMap.adjoint weightedVolterraOperator
        (weightedHartreeOrthonormalSineMode n) =
      (weightedVolterraSineScale n)⁻¹ • weightedVolterraSineMode n := by
  unfold weightedVolterraSineMode
  rw [smul_smul, inv_mul_cancel₀ (sineScale_pos n).ne', one_smul]

/-- Each actual output coefficient is the corresponding input coefficient
times the singular value, for every L2 input. -/
theorem weightedVolterraSineMode_inner (n : ℕ) (f : RealL2 halfLineMeasure) :
    inner ℝ (weightedHartreeOrthonormalSineMode n) (weightedVolterraOperator f) =
      (weightedVolterraSineScale n)⁻¹ * inner ℝ (weightedVolterraSineMode n) f := by
  rw [← ContinuousLinearMap.adjoint_inner_left,
    weightedVolterraOperator_adjoint_sineMode, real_inner_smul_left]

/-- The transferred modes are actual eigenvectors of the input Gram
operator `V* V`, with the same positive Green multipliers. -/
theorem weightedVolterraGram_sineMode (n : ℕ) :
    ContinuousLinearMap.adjoint weightedVolterraOperator
        (weightedVolterraOperator (weightedVolterraSineMode n)) =
      (1 / (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1)) • weightedVolterraSineMode n := by
  rw [weightedVolterraOperator_sineMode, map_smul,
    weightedVolterraOperator_adjoint_sineMode, smul_smul]
  congr 1
  rw [← sineScale_sq n]
  simp only [one_div, pow_two, mul_inv_rev]

/-- The actual transferred coefficients are square summable and satisfy
Bessel's inequality on the full input L2 space.  Completeness of the
transferred family and injectivity of `V` are not assumed. -/
theorem weightedVolterraSineMode_bessel (f : RealL2 halfLineMeasure) :
    Summable (fun n : ℕ => (inner ℝ (weightedVolterraSineMode n) f) ^ 2) ∧
      (∑' n : ℕ, (inner ℝ (weightedVolterraSineMode n) f) ^ 2) ≤ ‖f‖ ^ 2 := by
  constructor
  · simpa only [Real.norm_eq_abs, sq_abs] using
      weightedVolterraSineMode_orthonormal.inner_products_summable f
  · simpa only [Real.norm_eq_abs, sq_abs] using
      weightedVolterraSineMode_orthonormal.tsum_inner_products_le f

end HBL.Modulation.Monopole
