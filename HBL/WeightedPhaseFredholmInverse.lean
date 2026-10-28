import HBL.WeightedPhaseFredholmCore
import HBL.FredholmCokernelAlternative

/-!
# Actual phase-channel normalized Fredholm inverse

The compact operator is the concrete weighted free Green map multiplied by
three. Its exact one-dimensional kernel and adjoint kernel were established
in WeightedPhaseFredholmCore. Here the complete Fredholm alternative gives
a unique canonical correction for every compatible half-line L2 source.
No arbitrary inverse parameter or new axiom is introduced.
-/

noncomputable section
set_option autoImplicit false

open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- Compatibility is orthogonality to the real, genuine first sine mode. -/
theorem phaseFredholmSource_mem_cokernel_orthogonal
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ (weightedHartreeSineModeL2 1) F = 0) :
    F ∈ (ContinuousLinearMap.adjoint (1 - weightedPhaseBirman)).kerᗮ := by
  rw [weightedPhaseFredholm_adjointKernel_eq_sine_span,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact hF

theorem phaseFredholmSource_mem_range_iff
    (F : RealL2 halfLineMeasure) :
    F ∈ (1 - weightedPhaseBirman).range ↔
      inner ℝ (weightedHartreeSineModeL2 1) F = 0 := by
  rw [HBL.Fredholm.one_sub_range_eq_adjointKernel_orthogonal
    (K := weightedPhaseBirman) weightedPhaseBirman_compact,
    weightedPhaseFredholm_adjointKernel_eq_sine_span,
    Submodule.mem_orthogonal_singleton_iff_inner_right]

theorem existsUnique_phaseFredholmSolution
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ (weightedHartreeSineModeL2 1) F = 0) :
    ∃! x : (1 - weightedPhaseBirman).kerᗮ,
      (1 - weightedPhaseBirman) (x : RealL2 halfLineMeasure) = F :=
  HBL.Fredholm.existsUnique_one_sub_apply_eq_of_mem_adjointKernel_orthogonal
    weightedPhaseBirman_compact
    (phaseFredholmSource_mem_cokernel_orthogonal F hF)

def phaseFredholmSolution
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ (weightedHartreeSineModeL2 1) F = 0) :
    (1 - weightedPhaseBirman).kerᗮ :=
  Classical.choose (existsUnique_phaseFredholmSolution F hF)

theorem phaseFredholmSolution_equation
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ (weightedHartreeSineModeL2 1) F = 0) :
    (1 - weightedPhaseBirman)
        (phaseFredholmSolution F hF : RealL2 halfLineMeasure) = F :=
  (Classical.choose_spec (existsUnique_phaseFredholmSolution F hF)).1

theorem phaseFredholmSolution_unique
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ (weightedHartreeSineModeL2 1) F = 0)
    (x : (1 - weightedPhaseBirman).kerᗮ)
    (hx : (1 - weightedPhaseBirman) (x : RealL2 halfLineMeasure) = F) :
    x = phaseFredholmSolution F hF :=
  (Classical.choose_spec (existsUnique_phaseFredholmSolution F hF)).2 x hx

theorem phaseFredholmSolution_green_equation
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ (weightedHartreeSineModeL2 1) F = 0) :
    (phaseFredholmSolution F hF : RealL2 halfLineMeasure) =
      (3 : ℝ) • weightedFreeGreenOperator
        (phaseFredholmSolution F hF : RealL2 halfLineMeasure) + F := by
  have heq := phaseFredholmSolution_equation F hF
  change
    (phaseFredholmSolution F hF : RealL2 halfLineMeasure) -
      weightedPhaseBirman
        (phaseFredholmSolution F hF : RealL2 halfLineMeasure) = F at heq
  have hsum := (sub_eq_iff_eq_add).mp heq
  simpa only [weightedPhaseBirman, ContinuousLinearMap.smul_apply, add_comm] using hsum

#print axioms phaseFredholmSource_mem_range_iff
#print axioms existsUnique_phaseFredholmSolution
#print axioms phaseFredholmSolution_equation
#print axioms phaseFredholmSolution_unique
#print axioms phaseFredholmSolution_green_equation

end HBL.Modulation.Monopole
