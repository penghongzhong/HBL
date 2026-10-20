import HBL.WeightedHartreeSquareIdentity
import HBL.WeightedHartreeSineNorm

/-!
The actual Green and Birman--Schwinger actions follow algebraically from
the unconditional Hartree square identity and self-adjointness. No
completeness statement or additional Fourier expansion is required.
-/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem weightedHartreeSquareGreen_reverse
    (x : RealL2 halfLineMeasure) :
    weightedHartreeOperator (weightedHartreeOperator x) +
        weightedFreeGreenOperator
          (weightedHartreeOperator (weightedHartreeOperator x)) =
      (576 : ℝ) • weightedFreeGreenOperator x := by
  have hT : ∀ u v : RealL2 halfLineMeasure,
      inner ℝ (weightedHartreeOperator u) v =
        inner ℝ u (weightedHartreeOperator v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedHartreeOperator_selfAdjoint
  have hG : ∀ u v : RealL2 halfLineMeasure,
      inner ℝ (weightedFreeGreenOperator u) v =
        inner ℝ u (weightedFreeGreenOperator v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedFreeGreenOperator_selfAdjoint
  apply ext_inner_left ℝ
  intro y
  calc
    inner ℝ y (weightedHartreeOperator (weightedHartreeOperator x) +
        weightedFreeGreenOperator
          (weightedHartreeOperator (weightedHartreeOperator x))) =
        inner ℝ (y + weightedFreeGreenOperator y)
          (weightedHartreeOperator (weightedHartreeOperator x)) := by
      rw [inner_add_right, inner_add_left, hG]
    _ = inner ℝ (weightedHartreeOperator
          (weightedHartreeOperator (y + weightedFreeGreenOperator y))) x := by
      rw [hT, hT]
    _ = inner ℝ ((576 : ℝ) • weightedFreeGreenOperator y) x := by
      rw [weightedHartreeSquareGreenIdentity y]
    _ = inner ℝ y ((576 : ℝ) • weightedFreeGreenOperator x) := by
      rw [real_inner_smul_left, real_inner_smul_right, hG]

/-- The actual free Green operator acts on every positive sine mode with
the multiplier forced by the proved Hartree square identity. -/
theorem weightedFreeGreenOperator_sineMode (n : ℕ) (hn : 0 < n) :
    weightedFreeGreenOperator (weightedHartreeSineModeL2 n) =
      (1 / (4 * (n : ℝ) ^ 2 - 1)) • weightedHartreeSineModeL2 n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < 4 * (n : ℝ) ^ 2 - 1 := by nlinarith
  have hs := weightedHartreeSquareGreen_reverse (weightedHartreeSineModeL2 n)
  simp only [weightedHartreeOperator_sineMode n hn, map_smul, smul_smul] at hs
  apply ext_inner_left ℝ
  intro y
  have heq := congrArg (fun z => inner ℝ y z) hs
  simp only [inner_add_right, real_inner_smul_right] at heq
  rw [real_inner_smul_right]
  field_simp [hn0] at heq
  field_simp [hd.ne']
  nlinarith only [heq]

/-- The actual Birman--Schwinger composition is `G ∘ (9 I + T)`, giving
its explicit multiplier on the same nonzero radial sine modes. -/
theorem weightedBirmanSchwingerOperator_sineMode (n : ℕ) (hn : 0 < n) :
    weightedBirmanSchwingerOperator (weightedHartreeSineModeL2 n) =
      ((9 + 12 / (n : ℝ)) / (4 * (n : ℝ) ^ 2 - 1)) •
        weightedHartreeSineModeL2 n := by
  change weightedFreeGreenOperator
      ((9 : ℝ) • weightedHartreeSineModeL2 n +
        weightedHartreeOperator (weightedHartreeSineModeL2 n)) = _
  rw [weightedHartreeOperator_sineMode n hn, ← add_smul, map_smul,
    weightedFreeGreenOperator_sineMode n hn, smul_smul]
  congr 1
  ring

/-- Both actions are genuine eigenvectors of the existing operators:
the L2 sine mode is nonzero, as established by its exact squared norm. -/
theorem weightedGreenSineMode_hasEigenvectors (n : ℕ) (hn : 0 < n) :
    Module.End.HasEigenvector weightedFreeGreenOperator.toLinearMap
        (1 / (4 * (n : ℝ) ^ 2 - 1)) (weightedHartreeSineModeL2 n) ∧
      Module.End.HasEigenvector weightedBirmanSchwingerOperator.toLinearMap
        ((9 + 12 / (n : ℝ)) / (4 * (n : ℝ) ^ 2 - 1))
        (weightedHartreeSineModeL2 n) := by
  constructor
  · apply Module.End.hasEigenvector_iff.mpr
    exact ⟨Module.End.mem_eigenspace_iff.mpr (weightedFreeGreenOperator_sineMode n hn),
      weightedHartreeSineModeL2_ne_zero n hn⟩
  · apply Module.End.hasEigenvector_iff.mpr
    exact ⟨Module.End.mem_eigenspace_iff.mpr
        (weightedBirmanSchwingerOperator_sineMode n hn),
      weightedHartreeSineModeL2_ne_zero n hn⟩

end HBL.Modulation.Monopole
