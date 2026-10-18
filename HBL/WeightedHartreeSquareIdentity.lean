import HBL.WeightedZeroGreenOperator
import HBL.WeightedBirmanSchwingerPolynomial

/-!
Unconditional closure of the weighted Green--Hartree spectral bridge.
-/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

theorem weightedHartreeSquareGreenIdentity :
    WeightedHartreeSquareGreenIdentity := by
  intro z
  have hsquare := congrArg
    (fun T : RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure =>
      T (z + weightedFreeGreenOperator z))
    weightedHartreeOperator_square
  simp only [ContinuousLinearMap.comp_apply, smul_apply] at hsquare
  calc
    weightedHartreeOperator
        (weightedHartreeOperator (z + weightedFreeGreenOperator z)) =
        (576 : ℝ) •
          weightedZeroGreenOperator (z + weightedFreeGreenOperator z) :=
      hsquare
    _ = (576 : ℝ) • weightedFreeGreenOperator z := by
      rw [weightedZeroGreen_resolvent]

theorem weightedBirmanSchwinger_fixed_mem_span
    (x : RealL2 halfLineMeasure)
    (hfixed : weightedBirmanSchwingerOperator x = x) :
    x ∈ Submodule.span ℝ {weightedScaleResonanceL2} :=
  weightedBirmanSchwinger_fixed_mem_span_of_square_identity
    weightedHartreeSquareGreenIdentity x hfixed

theorem weightedBirmanSchwinger_fixed_iff_span
    (x : RealL2 halfLineMeasure) :
    weightedBirmanSchwingerOperator x = x ↔
      x ∈ Submodule.span ℝ {weightedScaleResonanceL2} :=
  weightedBirmanSchwinger_fixed_iff_span_of_square_identity
    weightedHartreeSquareGreenIdentity x

theorem weightedBirmanSchwinger_adjointKernel_eq_scale_span :
    (ContinuousLinearMap.id ℝ (RealL2 halfLineMeasure) -
      ContinuousLinearMap.adjoint weightedBirmanSchwingerOperator).ker =
        Submodule.span ℝ
          {weightedPotentialOperator weightedScaleResonanceL2} :=
  weightedBirmanSchwinger_adjointKernel_eq_span
    weightedScaleResonanceL2 weightedBirmanSchwinger_fixed_iff_span

end HBL.Modulation.Monopole
