import HBL.WeightedHartreeSineModes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
Exact norm and nonzero eigenvector certification for the already constructed
radial Hartree sine modes. The calculation uses the actual arctangent
Jacobian and the elementary sine-square integral, without a Fourier
completeness assumption or a new model operator.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole
open HBL.L2Kernel
open HBL.Modulation.AffineTail

private theorem sineSquare_half_integral (n : ℕ) (hn : 0 < n) :
    (∫ theta : ℝ in 0..Real.pi / 2,
      Real.sin (2 * (n : ℝ) * theta) ^ 2) = Real.pi / 4 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hscale := intervalIntegral.integral_comp_mul_left
    (f := fun x : ℝ => Real.sin x ^ 2)
    (a := 0) (b := Real.pi / 2) (c := 2 * (n : ℝ)) (by positivity)
  rw [mul_zero, show 2 * (n : ℝ) * (Real.pi / 2) = (n : ℝ) * Real.pi by ring,
    integral_sin_sq, Real.sin_zero, Real.sin_nat_mul_pi] at hscale
  simp only [zero_mul, sub_zero, smul_eq_mul] at hscale
  rw [hscale]
  field_simp [hn0]
  ring

/-- The existing L2 mode has exact positive squared norm pi/4. -/
theorem weightedHartreeSineModeL2_inner_self (n : ℕ) (hn : 0 < n) :
    inner ℝ (weightedHartreeSineModeL2 n) (weightedHartreeSineModeL2 n) =
      Real.pi / 4 := by
  rw [L2.inner_def]
  calc
    (∫ r : ℝ, inner ℝ (weightedHartreeSineModeL2 n r) (weightedHartreeSineModeL2 n r)
        ∂halfLineMeasure) =
        ∫ r in Ioi (0 : ℝ), bubble r ^ 2 *
          Real.sin (2 * (n : ℝ) * Real.arctan r) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [weightedHartreeSineModeL2_ae n] with r hr
      rw [hr, Real.inner_apply]
      unfold weightedHartreeSineMode
      ring
    _ = ∫ theta : ℝ in 0..Real.pi / 2,
        Real.sin (2 * (n : ℝ) * theta) ^ 2 := by
      rw [intervalIntegral_eq_integral_Ioi_arctan]
    _ = Real.pi / 4 := sineSquare_half_integral n hn

/-- Nonzeroness is proved in the actual L2 quotient, not just at one point
of a chosen representative. -/
theorem weightedHartreeSineModeL2_ne_zero (n : ℕ) (hn : 0 < n) :
    weightedHartreeSineModeL2 n ≠ 0 := by
  intro hz
  have h := weightedHartreeSineModeL2_inner_self n hn
  rw [hz, inner_zero_left] at h
  linarith [Real.pi_pos]

/-- Each positive-index mode is a genuine nonzero eigenvector of the existing
weighted Hartree operator with eigenvalue 12/n. -/
theorem weightedHartreeSineModeL2_hasEigenvector (n : ℕ) (hn : 0 < n) :
    Module.End.HasEigenvector weightedHartreeOperator.toLinearMap
      (12 / (n : ℝ)) (weightedHartreeSineModeL2 n) := by
  apply Module.End.hasEigenvector_iff.mpr
  exact ⟨Module.End.mem_eigenspace_iff.mpr (weightedHartreeOperator_sineMode n hn),
    weightedHartreeSineModeL2_ne_zero n hn⟩

end HBL.Modulation.Monopole
