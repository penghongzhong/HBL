import HBL.WeightedVolterraAPlusKernel
import HBL.WeightedBirmanSineBounds

/-!
HBL: short diagonalization of the ACTUAL bounded
Volterra-channel A₊ᵛ on the transferred orthonormal singular vectors.

No new axioms or abstract PDE assumptions are introduced. The fixed toolchain is Lean 4.35.0-rc3 / Mathlib a98628e1.
This does not identify the physical radial Hessian or close HBL's main
blowup theorem.
-/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem weightedPotential_orthonormalSineMode (n : ℕ) :
    weightedPotentialOperator (weightedHartreeOrthonormalSineMode n) =
      (9 + 12 / ((n + 1 : ℕ) : ℝ)) •
        weightedHartreeOrthonormalSineMode n := by
  change (9 : ℝ) • weightedHartreeOrthonormalSineMode n +
    weightedHartreeOperator (weightedHartreeOrthonormalSineMode n) = _
  rw [weightedHartreeOperator_orthonormalSineMode, ← add_smul]

/-- The finite-dimensional calculation on each actual transferred mode,
using only the already-verified singular-vector identities. -/
theorem weightedVolterraAPlus_sineMode_raw (n : ℕ) :
    weightedVolterraAPlus (weightedVolterraSineMode n) =
      (1 - (weightedVolterraSineScale n)⁻¹ ^ 2 *
          (9 + 12 / ((n + 1 : ℕ) : ℝ))) •
        weightedVolterraSineMode n := by
  change weightedVolterraSineMode n -
      ContinuousLinearMap.adjoint weightedVolterraOperator
        (weightedPotentialOperator
          (weightedVolterraOperator (weightedVolterraSineMode n))) = _
  simp only [weightedVolterraOperator_sineMode, map_smul,
    weightedPotential_orthonormalSineMode,
    weightedVolterraOperator_adjoint_sineMode, smul_smul]
  module

/-- Spectral multiplier in exactly the normalization of the published
weighted Birman-Schwinger sine coefficients. -/
theorem weightedVolterraAPlus_sineMode (n : ℕ) :
    weightedVolterraAPlus (weightedVolterraSineMode n) =
      (1 - weightedBirmanSineCoefficient n) •
        weightedVolterraSineMode n := by
  rw [weightedVolterraAPlus_sineMode_raw]
  congr 1
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hd : 0 ≤ 4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1 := by
    nlinarith
  have hsq : weightedVolterraSineScale n ^ 2 =
      4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1 :=
    Real.sq_sqrt hd
  unfold weightedBirmanSineCoefficient
  rw [inv_pow, mul_comm, ← div_eq_mul_inv, hsq]

/-- The first actual transferred sine vector is a negative mode of A₊ᵛ. -/
theorem weightedVolterraAPlus_negative_sineMode :
    weightedVolterraAPlus (weightedVolterraSineMode 0) =
      (-6 : ℝ) • weightedVolterraSineMode 0 := by
  rw [weightedVolterraAPlus_sineMode, weightedBirmanSineCoefficient_zero]
  norm_num

/-- The second actual transferred sine vector is a zero mode of A₊ᵛ. -/
theorem weightedVolterraAPlus_zero_sineMode :
    weightedVolterraAPlus (weightedVolterraSineMode 1) = 0 := by
  rw [weightedVolterraAPlus_sineMode, weightedBirmanSineCoefficient_one]
  simp

/-- The exact kernel is the span of the second transferred sine mode. -/
theorem weightedVolterraAPlus_kernel_eq_sine_span :
    weightedVolterraAPlus.ker =
      Submodule.span ℝ {weightedVolterraSineMode 1} := by
  have hn : weightedVolterraSineMode 1 ≠ 0 := by
    intro hzero
    have hnorm := weightedVolterraSineMode_orthonormal.norm_eq_one 1
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hmem : weightedVolterraSineMode 1 ∈
      Submodule.span ℝ {weightedVolterraScaleVector} := by
    rw [← weightedVolterraAPlus_kernel_eq_span]
    exact weightedVolterraAPlus_zero_sineMode
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc0 : c ≠ 0 := by
    intro hz
    apply hn
    rw [hz, zero_smul] at hc
    exact hc.symm
  rw [weightedVolterraAPlus_kernel_eq_span, ← hc]
  exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0) _).symm

/-- The actual Volterra-channel kernel has dimension one. -/
theorem weightedVolterraAPlus_kernel_finrank :
    Module.finrank ℝ weightedVolterraAPlus.ker = 1 := by
  rw [weightedVolterraAPlus_kernel_eq_span]
  exact finrank_span_singleton weightedVolterraScaleVector_ne_zero

/-- The first transferred unit vector is strictly negative for the actual form. -/
theorem weightedVolterraAPlus_negative_quadratic :
    inner ℝ (weightedVolterraAPlus (weightedVolterraSineMode 0))
      (weightedVolterraSineMode 0) = -6 := by
  rw [weightedVolterraAPlus_negative_sineMode, real_inner_smul_left,
    real_inner_self_eq_norm_sq, weightedVolterraSineMode_orthonormal.norm_eq_one]
  norm_num

end HBL.Modulation.Monopole
