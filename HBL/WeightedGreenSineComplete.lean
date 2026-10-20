import HBL.WeightedGreenEigenClassification
import HBL.WeightedHartreeSineOrthogonal
import HBL.WeightedFreeGreenInjective
import HBL.WeightedFreeGreenNonnegative
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Completeness of the actual normalized radial sine modes.

The compact self-adjoint spectral theorem is applied to the actual weighted
free Green operator.  Its zero kernel, absence of negative eigenvalues, and
positive eigenpair classification identify every eigenspace with a subspace
of the sine span.  No completeness assumption is introduced.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

theorem weightedHartreeSineModeL2_mem_orthonormal_span
    (n : ℕ) (hn : 0 < n) :
    weightedHartreeSineModeL2 n ∈
      Submodule.span ℝ (Set.range weightedHartreeOrthonormalSineMode) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hmem : weightedHartreeOrthonormalSineMode m ∈
      Submodule.span ℝ (Set.range weightedHartreeOrthonormalSineMode) :=
    Submodule.subset_span (Set.mem_range_self m)
  have hc : (2 / Real.sqrt Real.pi : ℝ) ≠ 0 :=
    div_ne_zero (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos).ne'
  exact (Submodule.smul_mem_iff _ hc).mp hmem

theorem weightedFreeGreen_positive_eigen_mem_orthonormal_span
    {mu : ℝ} (hmu : 0 < mu) (f : RealL2 halfLineMeasure)
    (heig : weightedFreeGreenOperator f = mu • f) :
    f ∈ Submodule.span ℝ (Set.range weightedHartreeOrthonormalSineMode) := by
  by_cases hf : f = 0
  · rw [hf]
    exact Submodule.zero_mem _
  obtain ⟨n, hn, _, hspan⟩ :=
    weightedFreeGreen_positive_eigen_classification hmu f hf heig
  exact (Submodule.span_le.mpr (by
    intro u hu
    rcases Set.mem_singleton_iff.mp hu with rfl
    exact weightedHartreeSineModeL2_mem_orthonormal_span n hn)) hspan

/-- Every eigenspace of the actual compact Green operator lies in the
algebraic span of the actual normalized sine family. -/
theorem weightedFreeGreen_eigenspace_le_orthonormal_span (mu : ℝ) :
    Module.End.eigenspace
        (weightedFreeGreenOperator : Module.End ℝ (RealL2 halfLineMeasure)) mu ≤
      Submodule.span ℝ (Set.range weightedHartreeOrthonormalSineMode) := by
  intro f hf
  have heig : weightedFreeGreenOperator f = mu • f :=
    Module.End.mem_eigenspace_iff.mp hf
  by_cases hf0 : f = 0
  · rw [hf0]
    exact Submodule.zero_mem _
  have hmu0 : mu ≠ 0 := by
    intro hzero
    apply hf0
    apply (weightedFreeGreenOperator_eq_zero_iff f).mp
    simpa [hzero] using heig
  exact weightedFreeGreen_positive_eigen_mem_orthonormal_span
    (weightedFreeGreen_nonzero_eigenvalue_pos mu f hf0 hmu0 heig) f heig

/-- The actual normalized sine family has trivial orthogonal complement.
The compact self-adjoint spectral theorem is used only after every Green
eigenspace, including the zero and negative cases, has been accounted for. -/
theorem weightedHartreeOrthonormalSineMode_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range weightedHartreeOrthonormalSineMode))ᗮ = ⊥ := by
  have hsym : weightedFreeGreenOperator.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedFreeGreenOperator_selfAdjoint
  apply eq_bot_iff.mpr
  calc
    (Submodule.span ℝ (Set.range weightedHartreeOrthonormalSineMode))ᗮ ≤
        (⨆ mu : ℝ, Module.End.eigenspace
          (weightedFreeGreenOperator : Module.End ℝ (RealL2 halfLineMeasure)) mu)ᗮ :=
      Submodule.orthogonal_le
        (iSup_le weightedFreeGreen_eigenspace_le_orthonormal_span)
    _ = ⊥ := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      weightedFreeGreenOperator_compact hsym

/-- Completeness in the actual radial L2 Hilbert space. -/
theorem weightedHartreeOrthonormalSineMode_dense_span :
    (Submodule.span ℝ (Set.range weightedHartreeOrthonormalSineMode)).topologicalClosure =
      ⊤ := by
  exact Submodule.topologicalClosure_eq_top_iff.mpr
    weightedHartreeOrthonormalSineMode_orthogonal_eq_bot

/-- The complete orthonormal basis furnished by the actual radial sine modes. -/
def weightedHartreeSineHilbertBasis : HilbertBasis ℕ ℝ (RealL2 halfLineMeasure) :=
  HilbertBasis.mkOfOrthogonalEqBot
    weightedHartreeOrthonormalSineMode_orthonormal
    weightedHartreeOrthonormalSineMode_orthogonal_eq_bot

@[simp]
theorem weightedHartreeSineHilbertBasis_apply (n : ℕ) :
    weightedHartreeSineHilbertBasis n = weightedHartreeOrthonormalSineMode n := by
  simp [weightedHartreeSineHilbertBasis]

/-- Every actual radial L2 vector is the L2 sum of its sine coefficients. -/
theorem weightedHartreeSine_hasSum (f : RealL2 halfLineMeasure) :
    HasSum (fun n : ℕ =>
      inner ℝ (weightedHartreeOrthonormalSineMode n) f •
        weightedHartreeOrthonormalSineMode n) f := by
  simpa only [HilbertBasis.repr_apply_apply, weightedHartreeSineHilbertBasis_apply] using
    weightedHartreeSineHilbertBasis.hasSum_repr f

/-- Parseval's identity for the actual normalized radial sine family. -/
theorem weightedHartreeSine_hasSum_sq (f : RealL2 halfLineMeasure) :
    HasSum (fun n : ℕ =>
      (inner ℝ (weightedHartreeOrthonormalSineMode n) f) ^ 2) (‖f‖ ^ 2) := by
  convert weightedHartreeSineHilbertBasis.hasSum_inner_mul_inner f f using 1
  · funext n
    rw [weightedHartreeSineHilbertBasis_apply, real_inner_comm f, pow_two]
  · exact (real_inner_self_eq_norm_sq f).symm

end HBL.Modulation.Monopole
