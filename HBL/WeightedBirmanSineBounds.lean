import HBL.WeightedGreenSineComplete

/-!
Quantitative bounds for the actual weighted Birman--Schwinger operator.

The already verified sine Hilbert basis and the actual Green/Hartree
operators are used throughout.  The two excluded coordinates are the
positive modes 1 and 2, indexed by 0 and 1 in the normalized family.
No energy-space identification or physical Hessian conclusion is asserted.
-/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The multiplier of the actual Birman--Schwinger operator on normalized
sine mode `n`, whose positive frequency is `n + 1`. -/
def weightedBirmanSineCoefficient (n : ℕ) : ℝ :=
  (9 + 12 / ((n + 1 : ℕ) : ℝ)) / (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1)

@[simp]
theorem weightedBirmanSineCoefficient_zero :
    weightedBirmanSineCoefficient 0 = 7 := by
  norm_num [weightedBirmanSineCoefficient]

@[simp]
theorem weightedBirmanSineCoefficient_one :
    weightedBirmanSineCoefficient 1 = 1 := by
  norm_num [weightedBirmanSineCoefficient]

/-- Every actual sine multiplier is strictly positive. -/
theorem weightedBirmanSineCoefficient_pos (n : ℕ) :
    0 < weightedBirmanSineCoefficient n := by
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hd : 0 < 4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1 := by nlinarith
  unfold weightedBirmanSineCoefficient
  exact div_pos (by positivity) hd

/-- The uniform sharp tail coefficient bound, starting at positive
frequency 3.  The first two multipliers are 7 and 1. -/
theorem weightedBirmanSineCoefficient_tail_le (n : ℕ) (hn : 2 ≤ n) :
    weightedBirmanSineCoefficient n ≤ (13 / 35 : ℝ) := by
  have hn3 : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hn
  have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  have hd : 0 < 4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1 := by nlinarith
  have hnum : 12 / ((n + 1 : ℕ) : ℝ) ≤ (4 : ℝ) := by
    apply (div_le_iff₀ hn0).mpr
    linarith
  unfold weightedBirmanSineCoefficient
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- The existing actual Birman--Schwinger sine action, with exactly the
normalization of the verified Hilbert basis. -/
theorem weightedBirmanSchwingerOperator_orthonormalSineMode (n : ℕ) :
    weightedBirmanSchwingerOperator (weightedHartreeOrthonormalSineMode n) =
      weightedBirmanSineCoefficient n • weightedHartreeOrthonormalSineMode n := by
  unfold weightedHartreeOrthonormalSineMode weightedBirmanSineCoefficient
  rw [map_smul, weightedBirmanSchwingerOperator_sineMode (n + 1) (Nat.succ_pos n),
    smul_smul, smul_smul]
  congr 1
  ring

private theorem weightedFreeGreen_orthonormalSineMode (n : ℕ) :
    weightedFreeGreenOperator (weightedHartreeOrthonormalSineMode n) =
      (1 / (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1)) •
        weightedHartreeOrthonormalSineMode n := by
  unfold weightedHartreeOrthonormalSineMode
  rw [map_smul, weightedFreeGreenOperator_sineMode (n + 1) (Nat.succ_pos n),
    smul_smul, smul_smul]
  congr 1
  ring

/-- The coefficient of `B f` is the actual multiplier times the
coefficient of `f`.  Symmetry of the actual factors, not an assumed
diagonal model or completeness hypothesis, proves this identity. -/
theorem weightedBirmanSchwinger_inner_orthonormalSineMode
    (n : ℕ) (f : RealL2 halfLineMeasure) :
    inner ℝ (weightedHartreeOrthonormalSineMode n) (weightedBirmanSchwingerOperator f) =
      weightedBirmanSineCoefficient n *
        inner ℝ (weightedHartreeOrthonormalSineMode n) f := by
  have hG : ∀ u v : RealL2 halfLineMeasure,
      inner ℝ (weightedFreeGreenOperator u) v =
        inner ℝ u (weightedFreeGreenOperator v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedFreeGreenOperator_selfAdjoint
  have hP : ∀ u v : RealL2 halfLineMeasure,
      inner ℝ (weightedPotentialOperator u) v =
        inner ℝ u (weightedPotentialOperator v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedPotentialOperator_selfAdjoint
  have heP : weightedPotentialOperator (weightedHartreeOrthonormalSineMode n) =
      (9 + 12 / ((n + 1 : ℕ) : ℝ)) • weightedHartreeOrthonormalSineMode n := by
    change (9 : ℝ) • weightedHartreeOrthonormalSineMode n +
      weightedHartreeOperator (weightedHartreeOrthonormalSineMode n) = _
    rw [weightedHartreeOperator_orthonormalSineMode, ← add_smul]
  change inner ℝ (weightedHartreeOrthonormalSineMode n)
    (weightedFreeGreenOperator (weightedPotentialOperator f)) = _
  rw [← hG (weightedHartreeOrthonormalSineMode n) (weightedPotentialOperator f),
    weightedFreeGreen_orthonormalSineMode, real_inner_smul_left,
    ← hP (weightedHartreeOrthonormalSineMode n) f, heP, real_inner_smul_left]
  unfold weightedBirmanSineCoefficient
  ring

/-- On the orthogonal complement of positive sine modes 1 and 2, the
actual weighted Birman--Schwinger operator has norm at most `13 / 35`.
The domain is the full actual radial `L²`, with no regularity assumptions. -/
theorem weightedBirmanSchwinger_norm_le_tail
    (f : RealL2 halfLineMeasure)
    (hfirst : inner ℝ (weightedHartreeOrthonormalSineMode 0) f = 0)
    (hsecond : inner ℝ (weightedHartreeOrthonormalSineMode 1) f = 0) :
    ‖weightedBirmanSchwingerOperator f‖ ≤ (13 / 35 : ℝ) * ‖f‖ := by
  have hsq : ‖weightedBirmanSchwingerOperator f‖ ^ 2 ≤
      (13 / 35 : ℝ) ^ 2 * ‖f‖ ^ 2 := by
    refine hasSum_le ?_ (weightedHartreeSine_hasSum_sq (weightedBirmanSchwingerOperator f))
      ((weightedHartreeSine_hasSum_sq f).mul_left ((13 / 35 : ℝ) ^ 2))
    intro n
    rw [weightedBirmanSchwinger_inner_orthonormalSineMode]
    by_cases hn0 : n = 0
    · subst n
      rw [hfirst]
      norm_num
    by_cases hn1 : n = 1
    · subst n
      rw [hsecond]
      norm_num
    have hn : 2 ≤ n := by omega
    have hc0 := (weightedBirmanSineCoefficient_pos n).le
    have hc := weightedBirmanSineCoefficient_tail_le n hn
    have hcsq : weightedBirmanSineCoefficient n ^ 2 ≤ (13 / 35 : ℝ) ^ 2 :=
      (sq_le_sq₀ hc0 (by norm_num)).mpr hc
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hcsq (sq_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [mul_pow] using hsq

/-- The actual weighted `I - B` quadratic form has the quantitative gap
`22 / 35` after removing positive modes 1 and 2.  This is an `L²`
operator statement; no physical radial energy identification is asserted. -/
theorem weightedBirmanSchwinger_tail_coercive
    (f : RealL2 halfLineMeasure)
    (hfirst : inner ℝ (weightedHartreeOrthonormalSineMode 0) f = 0)
    (hsecond : inner ℝ (weightedHartreeOrthonormalSineMode 1) f = 0) :
    (22 / 35 : ℝ) * ‖f‖ ^ 2 ≤
      inner ℝ (f - weightedBirmanSchwingerOperator f) f := by
  have hnorm := weightedBirmanSchwinger_norm_le_tail f hfirst hsecond
  have hinner := real_inner_le_norm (weightedBirmanSchwingerOperator f) f
  have hmul := mul_le_mul_of_nonneg_right hnorm (norm_nonneg f)
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  nlinarith

end HBL.Modulation.Monopole
