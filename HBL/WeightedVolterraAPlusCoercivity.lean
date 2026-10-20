import HBL.WeightedVolterraAPlusKernel
import HBL.WeightedBirmanSineBounds

/-!
HBL (UNCOMPILED / NOT ACCEPTED): exact quadratic form and quantitative
coercivity of the actual bounded Volterra-channel operator A₊ᵛ = I - V* P V.

The actual output sine Hilbert basis gives the exact potential quadratic
form. The transferred input family is used only through its already proved
Bessel inequality. Its completeness and injectivity of V are not assumed.
The statement concerns the concrete half-line L² operator. It does not
identify this operator with the physical radial Hessian and does not close
the main blowup theorem.

This independent candidate has not been compiled and must not be counted
as an accepted module. No new axioms or conclusion-shaped hypotheses are
introduced.
-/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem coercivity_potential_sineMode (n : ℕ) :
    weightedPotentialOperator (weightedHartreeOrthonormalSineMode n) =
      (9 + 12 / ((n + 1 : ℕ) : ℝ)) •
        weightedHartreeOrthonormalSineMode n := by
  change (9 : ℝ) • weightedHartreeOrthonormalSineMode n +
    weightedHartreeOperator (weightedHartreeOrthonormalSineMode n) = _
  rw [weightedHartreeOperator_orthonormalSineMode, ← add_smul]

private theorem coercivity_potential_inner_sineMode
    (n : ℕ) (f : RealL2 halfLineMeasure) :
    inner ℝ (weightedHartreeOrthonormalSineMode n) (weightedPotentialOperator f) =
      (9 + 12 / ((n + 1 : ℕ) : ℝ)) *
        inner ℝ (weightedHartreeOrthonormalSineMode n) f := by
  have hP : ∀ u v : RealL2 halfLineMeasure,
      inner ℝ (weightedPotentialOperator u) v =
        inner ℝ u (weightedPotentialOperator v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedPotentialOperator_selfAdjoint
  rw [← hP (weightedHartreeOrthonormalSineMode n) f,
    coercivity_potential_sineMode, real_inner_smul_left]

private theorem coercivity_singular_coefficient (n : ℕ) :
    (weightedVolterraSineScale n)⁻¹ ^ 2 *
        (9 + 12 / ((n + 1 : ℕ) : ℝ)) =
      weightedBirmanSineCoefficient n := by
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hd : 0 ≤ 4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1 := by
    nlinarith
  have hsq : weightedVolterraSineScale n ^ 2 =
      4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1 :=
    Real.sq_sqrt hd
  unfold weightedBirmanSineCoefficient
  rw [inv_pow, mul_comm, ← div_eq_mul_inv, hsq]

/-- Exact summable spectral expansion of the potential quadratic form for
an arbitrary input in the actual half-line L² space. Only the output
family must be complete. -/
theorem weightedVolterraPotential_hasSum (f : RealL2 halfLineMeasure) :
    HasSum (fun n : ℕ => weightedBirmanSineCoefficient n *
      (inner ℝ (weightedVolterraSineMode n) f) ^ 2)
      (inner ℝ (weightedPotentialOperator (weightedVolterraOperator f))
        (weightedVolterraOperator f)) := by
  convert weightedHartreeSineHilbertBasis.hasSum_inner_mul_inner
    (weightedPotentialOperator (weightedVolterraOperator f))
    (weightedVolterraOperator f) using 1
  funext n
  simp only [weightedHartreeSineHilbertBasis_apply]
  rw [real_inner_comm (weightedPotentialOperator (weightedVolterraOperator f)),
    coercivity_potential_inner_sineMode]
  simp only [weightedVolterraSineMode_inner]
  rw [← coercivity_singular_coefficient n]
  ring

/-- The exact quadratic form of the actual bounded Volterra-channel A₊ᵛ.
There is no claim that the transferred input modes form a complete basis. -/
theorem weightedVolterraAPlus_quadratic (f : RealL2 halfLineMeasure) :
    inner ℝ (weightedVolterraAPlus f) f =
      ‖f‖ ^ 2 - ∑' n : ℕ, weightedBirmanSineCoefficient n *
        (inner ℝ (weightedVolterraSineMode n) f) ^ 2 := by
  change inner ℝ (f - ContinuousLinearMap.adjoint weightedVolterraOperator
    (weightedPotentialOperator (weightedVolterraOperator f))) f = _
  rw [inner_sub_left, real_inner_self_eq_norm_sq,
    ContinuousLinearMap.adjoint_inner_left,
    (weightedVolterraPotential_hasSum f).tsum_eq]

/-- On the complement of the first two transferred modes, the potential
part is at most `13 / 35` times the full input L² norm squared. Bessel's
inequality accounts for any unspanned component of the input. -/
theorem weightedVolterraPotential_tail_le
    (f : RealL2 halfLineMeasure)
    (hfirst : inner ℝ (weightedVolterraSineMode 0) f = 0)
    (hsecond : inner ℝ (weightedVolterraSineMode 1) f = 0) :
    inner ℝ (weightedPotentialOperator (weightedVolterraOperator f))
        (weightedVolterraOperator f) ≤
      (13 / 35 : ℝ) * ‖f‖ ^ 2 := by
  obtain ⟨hsummable, hbessel⟩ := weightedVolterraSineMode_bessel f
  have hspectral :
      inner ℝ (weightedPotentialOperator (weightedVolterraOperator f))
          (weightedVolterraOperator f) ≤
        (13 / 35 : ℝ) *
          (∑' n : ℕ, (inner ℝ (weightedVolterraSineMode n) f) ^ 2) := by
    refine hasSum_le ?_ (weightedVolterraPotential_hasSum f)
      (hsummable.hasSum.mul_left (13 / 35 : ℝ))
    intro n
    by_cases hn0 : n = 0
    · subst n
      rw [hfirst]
      norm_num
    by_cases hn1 : n = 1
    · subst n
      rw [hsecond]
      norm_num
    have hn : 2 ≤ n := by omega
    exact mul_le_mul_of_nonneg_right
      (weightedBirmanSineCoefficient_tail_le n hn) (sq_nonneg _)
  exact hspectral.trans
    (mul_le_mul_of_nonneg_left hbessel (by norm_num : (0 : ℝ) ≤ 13 / 35))

/-- Quantitative `22 / 35` coercivity for the actual half-line L² operator,
after excluding its first two actual transferred sine modes. -/
theorem weightedVolterraAPlus_tail_coercive
    (f : RealL2 halfLineMeasure)
    (hfirst : inner ℝ (weightedVolterraSineMode 0) f = 0)
    (hsecond : inner ℝ (weightedVolterraSineMode 1) f = 0) :
    (22 / 35 : ℝ) * ‖f‖ ^ 2 ≤ inner ℝ (weightedVolterraAPlus f) f := by
  have hpotential := weightedVolterraPotential_tail_le f hfirst hsecond
  rw [weightedVolterraAPlus_quadratic, (weightedVolterraPotential_hasSum f).tsum_eq]
  linarith

end HBL.Modulation.Monopole
