import HBL.WeightedSourceFredholmBridge

/-!
# Normalized H+ Fredholm solve for arbitrary weighted source

For any physical L^{2,sigma} source with zero threshold charge, sigma>1,
the cross-space Green datum lies in the exact Fredholm range of the
concrete Birman--Schwinger operator.  We construct the unique solution
normalized perpendicular to the true fixed space.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

def weightedSourceFredholmRightHandSide
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    RealL2 halfLineMeasure :=
  weightedSourceGreenOperator sigma hsigma
    (weightedSourceDataL2 sigma F hF)

theorem weightedSourceFredholmRightHandSide_mem_range
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hcharge : channelPairing HartreeChannel.plus F = 0) :
    weightedSourceFredholmRightHandSide sigma hsigma F hF ∈
      (1 - weightedBirmanSchwingerOperator).range := by
  rw [HBL.Fredholm.one_sub_range_eq_adjointKernel_orthogonal
    (K := weightedBirmanSchwingerOperator)
    weightedBirmanSchwingerOperator_compact]
  exact weightedSourceGreen_mem_adjointKernel_orthogonal
    sigma hsigma F hF hcharge

theorem existsUnique_weightedSourceFredholmSolution
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hcharge : channelPairing HartreeChannel.plus F = 0) :
    ∃! x : (1 - weightedBirmanSchwingerOperator).kerᗮ,
      (1 - weightedBirmanSchwingerOperator)
          (x : RealL2 halfLineMeasure) =
        weightedSourceFredholmRightHandSide sigma hsigma F hF := by
  exact HBL.Fredholm.existsUnique_one_sub_apply_eq_of_mem_adjointKernel_orthogonal
    weightedBirmanSchwingerOperator_compact
    (weightedSourceGreen_mem_adjointKernel_orthogonal
      sigma hsigma F hF hcharge)

def weightedSourceFredholmSolution
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hcharge : channelPairing HartreeChannel.plus F = 0) :
    (1 - weightedBirmanSchwingerOperator).kerᗮ :=
  Classical.choose
    (existsUnique_weightedSourceFredholmSolution
      sigma hsigma F hF hcharge)

theorem weightedSourceFredholmSolution_equation
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hcharge : channelPairing HartreeChannel.plus F = 0) :
    (1 - weightedBirmanSchwingerOperator)
        (weightedSourceFredholmSolution sigma hsigma F hF hcharge :
          RealL2 halfLineMeasure) =
      weightedSourceFredholmRightHandSide sigma hsigma F hF :=
  (Classical.choose_spec
    (existsUnique_weightedSourceFredholmSolution
      sigma hsigma F hF hcharge)).1

theorem weightedSourceFredholmSolution_unique
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hcharge : channelPairing HartreeChannel.plus F = 0)
    (x : (1 - weightedBirmanSchwingerOperator).kerᗮ)
    (hx : (1 - weightedBirmanSchwingerOperator)
        (x : RealL2 halfLineMeasure) =
      weightedSourceFredholmRightHandSide sigma hsigma F hF) :
    x = weightedSourceFredholmSolution sigma hsigma F hF hcharge :=
  (Classical.choose_spec
    (existsUnique_weightedSourceFredholmSolution
      sigma hsigma F hF hcharge)).2 x hx

theorem weightedSourceFredholmSolution_green_equation
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hcharge : channelPairing HartreeChannel.plus F = 0) :
    (weightedSourceFredholmSolution sigma hsigma F hF hcharge :
        RealL2 halfLineMeasure) =
      weightedFreeGreenOperator
        (weightedPotentialOperator
          (weightedSourceFredholmSolution sigma hsigma F hF hcharge :
            RealL2 halfLineMeasure)) +
      weightedSourceFredholmRightHandSide sigma hsigma F hF := by
  have heq :=
    weightedSourceFredholmSolution_equation
      sigma hsigma F hF hcharge
  change
    (weightedSourceFredholmSolution sigma hsigma F hF hcharge :
        RealL2 halfLineMeasure) -
      weightedBirmanSchwingerOperator
        (weightedSourceFredholmSolution sigma hsigma F hF hcharge :
          RealL2 halfLineMeasure) =
      weightedSourceFredholmRightHandSide sigma hsigma F hF at heq
  unfold weightedBirmanSchwingerOperator at heq
  rw [ContinuousLinearMap.comp_apply] at heq
  exact (sub_eq_iff_eq_add).mp heq

#print axioms weightedSourceFredholmRightHandSide_mem_range
#print axioms existsUnique_weightedSourceFredholmSolution
#print axioms weightedSourceFredholmSolution_equation
#print axioms weightedSourceFredholmSolution_unique
#print axioms weightedSourceFredholmSolution_green_equation

end HBL.Modulation.Monopole
