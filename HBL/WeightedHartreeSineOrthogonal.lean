import HBL.WeightedHartreeSineNorm
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
Orthogonality follows from the symmetry of the actual weighted Hartree
operator and its already proved, distinct sine multipliers. No sine-product
integral or spectral completeness hypothesis is used here.
-/

noncomputable section

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

/-- Distinct positive integer sine modes are orthogonal in the actual radial
L2 space, by self-adjointness and the distinct eigenvalues `12 / n`. -/
theorem weightedHartreeSineModeL2_inner_eq_zero (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hne : n ≠ m) :
    inner ℝ (weightedHartreeSineModeL2 n) (weightedHartreeSineModeL2 m) = 0 := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    weightedHartreeOperator_selfAdjoint
  have heq := hsym (weightedHartreeSineModeL2 n) (weightedHartreeSineModeL2 m)
  change inner ℝ (weightedHartreeOperator (weightedHartreeSineModeL2 n))
      (weightedHartreeSineModeL2 m) =
    inner ℝ (weightedHartreeSineModeL2 n)
      (weightedHartreeOperator (weightedHartreeSineModeL2 m)) at heq
  rw [weightedHartreeOperator_sineMode n hn, weightedHartreeOperator_sineMode m hm,
    real_inner_smul_left, real_inner_smul_right] at heq
  have hcoeff : (12 / (n : ℝ)) ≠ 12 / (m : ℝ) := by
    intro h
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    field_simp [hn0, hm0] at h
    exact hne (Nat.cast_injective (show (n : ℝ) = (m : ℝ) by linarith))
  have hproduct : ((12 / (n : ℝ)) - 12 / (m : ℝ)) *
      inner ℝ (weightedHartreeSineModeL2 n) (weightedHartreeSineModeL2 m) = 0 := by
    nlinarith [heq]
  exact (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr hcoeff)

/-- Positive-index sine modes with their actual radial L2 normalization. -/
def weightedHartreeOrthonormalSineMode (n : ℕ) : RealL2 halfLineMeasure :=
  (2 / Real.sqrt Real.pi) • weightedHartreeSineModeL2 (n + 1)

/-- The normalized family retains the action of the same kernel operator. -/
theorem weightedHartreeOperator_orthonormalSineMode (n : ℕ) :
    weightedHartreeOperator (weightedHartreeOrthonormalSineMode n) =
      (12 / ((n + 1 : ℕ) : ℝ)) • weightedHartreeOrthonormalSineMode n := by
  unfold weightedHartreeOrthonormalSineMode
  rw [map_smul, weightedHartreeOperator_sineMode (n + 1) (Nat.succ_pos n),
    smul_smul, smul_smul]
  congr 1
  ring

/-- An orthonormal family of actual Hartree eigenvectors, indexed by all
natural numbers through the positive modes. Completeness is not asserted. -/
theorem weightedHartreeOrthonormalSineMode_orthonormal :
    Orthonormal ℝ weightedHartreeOrthonormalSineMode := by
  rw [orthonormal_iff_ite]
  intro n m
  by_cases hnm : n = m
  · subst m
    rw [ite_eq_left rfl]
    unfold weightedHartreeOrthonormalSineMode
    rw [real_inner_smul_left, real_inner_smul_right,
      weightedHartreeSineModeL2_inner_self (n + 1) (Nat.succ_pos n)]
    have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp [hpi]
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  · rw [ite_eq_right hnm]
    unfold weightedHartreeOrthonormalSineMode
    rw [real_inner_smul_left, real_inner_smul_right,
      weightedHartreeSineModeL2_inner_eq_zero (n + 1) (m + 1)
        (Nat.succ_pos n) (Nat.succ_pos m)
        (fun h => hnm (Nat.add_right_cancel h)), mul_zero, mul_zero]

end HBL.Modulation.Monopole
