import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
Solvability of `I - K` on the orthogonal complement of its fixed space.

This is the abstract functional-analytic step needed by the weighted
half-line inverse.  It is stated for a compact symmetric operator on a real
Hilbert space and produces the uniquely normalized solution, rather than
merely a range characterization.
-/

noncomputable section

open Module End

namespace HBL.Fredholm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Fixed space of a continuous linear endomorphism. -/
def fixedSpace (K : E →L[ℝ] E) : Submodule ℝ E :=
  eigenspace K.toLinearMap 1

/-- The normalization space perpendicular to all fixed vectors. -/
def fixedComplement (K : E →L[ℝ] E) : Submodule ℝ E :=
  (fixedSpace K)ᗮ

/-- A symmetric map preserves the perpendicular complement of its fixed
space. -/
theorem map_fixedComplement
    {K : E →L[ℝ] E} (hKsymm : K.IsSymmetric)
    (x : E) (hx : x ∈ fixedComplement K) :
    K x ∈ fixedComplement K := by
  simpa [fixedSpace, fixedComplement] using
    hKsymm.invariant_orthogonalComplement_eigenspace 1 x hx

/-- Restriction of a symmetric operator to the normalized complement. -/
def complementRestriction
    (K : E →L[ℝ] E) (hKsymm : K.IsSymmetric) :
    fixedComplement K →L[ℝ] fixedComplement K :=
  K.restrict (map_fixedComplement hKsymm)

theorem complementRestriction_compact
    {K : E →L[ℝ] E} (hKcompact : IsCompactOperator K)
    (hKsymm : K.IsSymmetric) :
    IsCompactOperator (complementRestriction K hKsymm) := by
  letI : CompleteSpace (fixedComplement K) :=
    (fixedSpace K).isClosed_orthogonal.completeSpace_coe
  exact hKcompact.restrict' (map_fixedComplement hKsymm)

theorem complementRestriction_no_fixed_vector
    {K : E →L[ℝ] E} (hKsymm : K.IsSymmetric) :
    ¬ HasEigenvalue
      ((complementRestriction K hKsymm).toLinearMap) 1 := by
  rw [hasEigenvalue_iff, not_ne_iff]
  simpa [complementRestriction] using
    (eigenspace_restrict_eq_bot
      (map_fixedComplement hKsymm) (fixedSpace K).orthogonal_disjoint)

/-- On the perpendicular complement of the fixed space, `I - K` is
bijective. -/
theorem one_sub_complementRestriction_bijective
    {K : E →L[ℝ] E} (hKcompact : IsCompactOperator K)
    (hKsymm : K.IsSymmetric) :
    Function.Bijective
      (1 - complementRestriction K hKsymm :
        fixedComplement K →L[ℝ] fixedComplement K) := by
  letI : CompleteSpace (fixedComplement K) :=
    (fixedSpace K).isClosed_orthogonal.completeSpace_coe
  have hres : (1 : ℝ) ∈
      resolventSet ℝ (complementRestriction K hKsymm) :=
    (IsCompactOperator.hasEigenvalue_or_mem_resolventSet
      (complementRestriction_compact hKcompact hKsymm)
      one_ne_zero).resolve_left
        (complementRestriction_no_fixed_vector hKsymm)
  rw [spectrum.mem_resolventSet_iff,
    ContinuousLinearMap.isUnit_iff_bijective] at hres
  simpa using hres

/-- Every datum perpendicular to the fixed space has a unique normalized
solution of `(I - K)x = f`. -/
theorem existsUnique_one_sub_apply_eq
    {K : E →L[ℝ] E} (hKcompact : IsCompactOperator K)
    (hKsymm : K.IsSymmetric) (f : fixedComplement K) :
    ∃! x : fixedComplement K,
      (1 - complementRestriction K hKsymm) x = f := by
  have hbij := one_sub_complementRestriction_bijective hKcompact hKsymm
  obtain ⟨x, hx⟩ := hbij.2 f
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hbij.1 (hy.trans hx.symm)

end HBL.Fredholm
