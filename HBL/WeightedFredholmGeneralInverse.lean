import HBL.MonopoleFredholmSolution

/-!
# General actual weighted Fredholm inverse for the real threshold channel

The previous monopole file applies the concrete Birman--Schwinger/Fredholm
machinery to one distinguished source.  The one-layer recursion needs the
same construction for an arbitrary compatible source at the current weight.
This file performs exactly that generalization for the already constructed
actual weighted Hartree operator.

There is no abstract right-inverse parameter and no new axiom: compatibility
is the genuine inner product with the verified scale resonance.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

def weightedFredholmRightHandSide
    (F : RealL2 halfLineMeasure) : RealL2 halfLineMeasure :=
  weightedFreeGreenOperator F

theorem weightedFredholmRightHandSide_mem_cokernel_orthogonal
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ weightedScaleResonanceL2 F = 0) :
    weightedFredholmRightHandSide F ∈
      (ContinuousLinearMap.adjoint
        (1 - weightedBirmanSchwingerOperator)).kerᗮ := by
  rw [adjoint_one_sub_weightedBirmanSchwinger_kernel,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  unfold weightedFredholmRightHandSide
  rw [weightedScaleResonance_cokernel_pairing]
  exact hF

theorem existsUnique_weightedFredholmSolve
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ weightedScaleResonanceL2 F = 0) :
    ∃! x : (1 - weightedBirmanSchwingerOperator).kerᗮ,
      (1 - weightedBirmanSchwingerOperator)
        (x : RealL2 halfLineMeasure) =
          weightedFredholmRightHandSide F :=
  HBL.Fredholm.existsUnique_one_sub_apply_eq_of_mem_adjointKernel_orthogonal
    weightedBirmanSchwingerOperator_compact
    (weightedFredholmRightHandSide_mem_cokernel_orthogonal F hF)

def weightedFredholmSolve
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ weightedScaleResonanceL2 F = 0) :
    (1 - weightedBirmanSchwingerOperator).kerᗮ :=
  Classical.choose (existsUnique_weightedFredholmSolve F hF)

theorem weightedFredholmSolve_equation
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ weightedScaleResonanceL2 F = 0) :
    (1 - weightedBirmanSchwingerOperator)
        (weightedFredholmSolve F hF : RealL2 halfLineMeasure) =
      weightedFredholmRightHandSide F :=
  (Classical.choose_spec (existsUnique_weightedFredholmSolve F hF)).1

theorem weightedFredholmSolve_unique
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ weightedScaleResonanceL2 F = 0)
    (x : (1 - weightedBirmanSchwingerOperator).kerᗮ)
    (hx : (1 - weightedBirmanSchwingerOperator)
        (x : RealL2 halfLineMeasure) =
      weightedFredholmRightHandSide F) :
    x = weightedFredholmSolve F hF :=
  (Classical.choose_spec (existsUnique_weightedFredholmSolve F hF)).2 x hx

/-- Green form of the normalized solution:
x = G(Px+F).  This is the exact weighted integral equation used by the
inner regional inverse. -/
theorem weightedFredholmSolve_eq_green
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ weightedScaleResonanceL2 F = 0) :
    (weightedFredholmSolve F hF : RealL2 halfLineMeasure) =
      weightedFreeGreenOperator
        (weightedPotentialOperator
            (weightedFredholmSolve F hF : RealL2 halfLineMeasure) + F) := by
  have heq := weightedFredholmSolve_equation F hF
  unfold weightedFredholmRightHandSide at heq
  change (weightedFredholmSolve F hF : RealL2 halfLineMeasure) -
      weightedBirmanSchwingerOperator
        (weightedFredholmSolve F hF : RealL2 halfLineMeasure) =
      weightedFreeGreenOperator F at heq
  unfold weightedBirmanSchwingerOperator at heq
  rw [ContinuousLinearMap.comp_apply] at heq
  rw [map_add]
  have hsum := (sub_eq_iff_eq_add).mp heq
  simpa only [add_comm] using hsum

/-- One terminal statement for the arbitrary compatible real inner source. -/
theorem weightedFredholmGeneralInverse_certified
    (F : RealL2 halfLineMeasure)
    (hF : inner ℝ weightedScaleResonanceL2 F = 0) :
    ∃! x : (1 - weightedBirmanSchwingerOperator).kerᗮ,
      (1 - weightedBirmanSchwingerOperator)
        (x : RealL2 halfLineMeasure) = weightedFreeGreenOperator F := by
  simpa only [weightedFredholmRightHandSide] using
    existsUnique_weightedFredholmSolve F hF

#print axioms weightedFredholmRightHandSide_mem_cokernel_orthogonal
#print axioms existsUnique_weightedFredholmSolve
#print axioms weightedFredholmSolve_equation
#print axioms weightedFredholmSolve_unique
#print axioms weightedFredholmSolve_eq_green
#print axioms weightedFredholmGeneralInverse_certified

end HBL.Modulation.Monopole
