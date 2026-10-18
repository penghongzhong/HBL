import HBL.MonopoleFredholmSolution
import HBL.WeightedScaleNonzero

/-!
Change from the canonical Hilbert normalization to a fixed continuous
linear normalization on the concrete half-line weighted L2 space.

The condition `ν weightedScaleResonanceL2 ≠ 0` says that the chosen
normalization detects the already identified one-dimensional fixed space.
It is explicitly retained in the normalization and uniqueness theorems.
The final theorem gives an admissible choice from the inner product, so
this condition concerns the fixed choice of normalization.
-/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- The Hilbert-normalized solution adjusted along the actual scaling
mode to satisfy a chosen continuous linear normalization. -/
def monopoleFredholmNormalizedSolution
    (ν : RealL2 halfLineMeasure →L[ℝ] ℝ) : RealL2 halfLineMeasure :=
  (monopoleFredholmSolution : RealL2 halfLineMeasure) -
    (ν (monopoleFredholmSolution : RealL2 halfLineMeasure) /
      ν weightedScaleResonanceL2) • weightedScaleResonanceL2

/-- Moving along the concrete fixed mode preserves the Fredholm equation. -/
theorem monopoleFredholmNormalizedSolution_equation
    (ν : RealL2 halfLineMeasure →L[ℝ] ℝ) :
    (1 - weightedBirmanSchwingerOperator)
        (monopoleFredholmNormalizedSolution ν) =
      monopoleFredholmRightHandSide := by
  have hscale :
      (1 - weightedBirmanSchwingerOperator) weightedScaleResonanceL2 = 0 := by
    change weightedScaleResonanceL2 -
      weightedBirmanSchwingerOperator weightedScaleResonanceL2 = 0
    rw [weightedBirmanSchwinger_scale_fixed, sub_self]
  unfold monopoleFredholmNormalizedSolution
  rw [map_sub, map_smul, monopoleFredholmSolution_equation,
    hscale, smul_zero, sub_zero]

theorem monopoleFredholmNormalizedSolution_normalization
    (ν : RealL2 halfLineMeasure →L[ℝ] ℝ)
    (hν : ν weightedScaleResonanceL2 ≠ 0) :
    ν (monopoleFredholmNormalizedSolution ν) = 0 := by
  unfold monopoleFredholmNormalizedSolution
  rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hν, sub_self]

/-- Uniqueness holds among all vectors of the actual L2 space.  The
difference of any two solutions is classified by the concrete fixed-space
theorem, and the chosen normalization removes that scalar freedom. -/
theorem monopoleFredholmNormalizedSolution_unique
    (ν : RealL2 halfLineMeasure →L[ℝ] ℝ)
    (hν : ν weightedScaleResonanceL2 ≠ 0)
    (x : RealL2 halfLineMeasure)
    (hx : (1 - weightedBirmanSchwingerOperator) x =
      monopoleFredholmRightHandSide)
    (hxν : ν x = 0) :
    x = monopoleFredholmNormalizedSolution ν := by
  have hdiff : (1 - weightedBirmanSchwingerOperator)
      (x - monopoleFredholmNormalizedSolution ν) = 0 := by
    rw [map_sub, hx, monopoleFredholmNormalizedSolution_equation, sub_self]
  have hfixed : weightedBirmanSchwingerOperator
      (x - monopoleFredholmNormalizedSolution ν) =
        x - monopoleFredholmNormalizedSolution ν := by
    change (x - monopoleFredholmNormalizedSolution ν) -
      weightedBirmanSchwingerOperator
        (x - monopoleFredholmNormalizedSolution ν) = 0 at hdiff
    exact (sub_eq_zero.mp hdiff).symm
  have hspan := (weightedBirmanSchwinger_fixed_iff_span
    (x - monopoleFredholmNormalizedSolution ν)).mp hfixed
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  have hcν : c * ν weightedScaleResonanceL2 = 0 := by
    have hpair := congrArg ν hc
    simpa only [map_smul, smul_eq_mul, map_sub, hxν,
      monopoleFredholmNormalizedSolution_normalization ν hν, sub_self] using hpair
  have hc0 : c = 0 := (mul_eq_zero.mp hcν).resolve_right hν
  rw [hc0, zero_smul] at hc
  exact sub_eq_zero.mp hc.symm

theorem existsUnique_monopoleFredholmNormalizedSolution
    (ν : RealL2 halfLineMeasure →L[ℝ] ℝ)
    (hν : ν weightedScaleResonanceL2 ≠ 0) :
    ∃! x : RealL2 halfLineMeasure,
      (1 - weightedBirmanSchwingerOperator) x = monopoleFredholmRightHandSide ∧
        ν x = 0 := by
  refine ⟨monopoleFredholmNormalizedSolution ν,
    ⟨monopoleFredholmNormalizedSolution_equation ν,
      monopoleFredholmNormalizedSolution_normalization ν hν⟩, ?_⟩
  intro x hx
  exact monopoleFredholmNormalizedSolution_unique ν hν x hx.1 hx.2

/-- Admissible continuous linear normalizations exist because the concrete
scaling mode is a nonzero L2 vector. -/
theorem exists_monopoleFredholmNormalizationFunctional :
    ∃ ν : RealL2 halfLineMeasure →L[ℝ] ℝ,
      ν weightedScaleResonanceL2 ≠ 0 := by
  refine ⟨innerSL ℝ weightedScaleResonanceL2, ?_⟩
  change inner ℝ weightedScaleResonanceL2 weightedScaleResonanceL2 ≠ 0
  exact inner_self_ne_zero.mpr weightedScaleResonanceL2_ne_zero

end HBL.Modulation.Monopole
