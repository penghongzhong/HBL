import HBL.WeightedVolterraSineModes
import HBL.WeightedHartreeSquareIdentity
import HBL.WeightedScaleNonzero

/-!
HBL: actual bounded Volterra-channel operator A₊ᵛ = I - V* P V.

It does not identify A₊ᵛ with the physical radial Hessian.
-/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The bounded Volterra-channel real operator; P is the already proved
conjugated real Hartree potential on the concrete half-line L². -/
def weightedVolterraAPlus :
    RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure :=
  ContinuousLinearMap.id ℝ (RealL2 halfLineMeasure) -
    ContinuousLinearMap.adjoint weightedVolterraOperator ∘L
      (weightedPotentialOperator ∘L weightedVolterraOperator)

/-- Self-adjointness of the actual Volterra-channel operator. -/
theorem weightedVolterraAPlus_selfAdjoint :
    IsSelfAdjoint weightedVolterraAPlus := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℝ (x - ContinuousLinearMap.adjoint weightedVolterraOperator
      (weightedPotentialOperator (weightedVolterraOperator x))) y =
    inner ℝ x (y - ContinuousLinearMap.adjoint weightedVolterraOperator
      (weightedPotentialOperator (weightedVolterraOperator y)))
  rw [inner_sub_left, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  have hP : inner ℝ (weightedPotentialOperator (weightedVolterraOperator x))
      (weightedVolterraOperator y) =
      inner ℝ (weightedVolterraOperator x)
        (weightedPotentialOperator (weightedVolterraOperator y)) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedPotentialOperator_selfAdjoint)
      (weightedVolterraOperator x) (weightedVolterraOperator y)
  exact congrArg (fun t : ℝ => inner ℝ x y - t) hP

/-- Generator of the kernel pulled back from the *actual* Birman fixed
vector, with no a priori injectivity hypothesis on V. -/
def weightedVolterraScaleVector : RealL2 halfLineMeasure :=
  ContinuousLinearMap.adjoint weightedVolterraOperator
    (weightedPotentialOperator weightedScaleResonanceL2)

/-- The generator is carried by V to the concrete fixed vector x₀. -/
theorem weightedVolterra_scale_image :
    weightedVolterraOperator weightedVolterraScaleVector =
      weightedScaleResonanceL2 := by
  calc
    weightedVolterraOperator weightedVolterraScaleVector =
        (weightedVolterraOperator ∘L
          ContinuousLinearMap.adjoint weightedVolterraOperator)
          (weightedPotentialOperator weightedScaleResonanceL2) := rfl
    _ = weightedFreeGreenOperator
          (weightedPotentialOperator weightedScaleResonanceL2) :=
        congrArg (fun T : RealL2 halfLineMeasure →L[ℝ]
          RealL2 halfLineMeasure =>
            T (weightedPotentialOperator weightedScaleResonanceL2))
          weightedVolterraOperator_comp_adjoint
    _ = weightedBirmanSchwingerOperator weightedScaleResonanceL2 := rfl
    _ = weightedScaleResonanceL2 := weightedBirmanSchwinger_scale_fixed

/-- The kernel generator is nonzero since its V-image is nonzero. -/
theorem weightedVolterraScaleVector_ne_zero :
    weightedVolterraScaleVector ≠ 0 := by
  intro hz
  have himage := weightedVolterra_scale_image
  rw [hz, map_zero] at himage
  exact weightedScaleResonanceL2_ne_zero himage.symm

/-- The *actual* bounded Volterra-channel A₊ has exactly the pulled-back
one-dimensional kernel. No completeness of transferred modes is used. -/
theorem weightedVolterraAPlus_kernel_eq_span :
    weightedVolterraAPlus.ker =
      Submodule.span ℝ {weightedVolterraScaleVector} := by
  ext ξ
  rw [LinearMap.mem_ker]
  change ξ - ContinuousLinearMap.adjoint weightedVolterraOperator
      (weightedPotentialOperator (weightedVolterraOperator ξ)) = 0 ↔
      ξ ∈ Submodule.span ℝ {weightedVolterraScaleVector}
  constructor
  · intro hξ
    have hrewrite : ξ = ContinuousLinearMap.adjoint weightedVolterraOperator
        (weightedPotentialOperator (weightedVolterraOperator ξ)) :=
      sub_eq_zero.mp hξ
    have hfixed : weightedBirmanSchwingerOperator
        (weightedVolterraOperator ξ) = weightedVolterraOperator ξ := by
      change weightedFreeGreenOperator
        (weightedPotentialOperator (weightedVolterraOperator ξ)) =
          weightedVolterraOperator ξ
      calc
        weightedFreeGreenOperator
            (weightedPotentialOperator (weightedVolterraOperator ξ)) =
            (weightedVolterraOperator ∘L
              ContinuousLinearMap.adjoint weightedVolterraOperator)
              (weightedPotentialOperator (weightedVolterraOperator ξ)) :=
          congrArg (fun T : RealL2 halfLineMeasure →L[ℝ]
            RealL2 halfLineMeasure =>
              T (weightedPotentialOperator (weightedVolterraOperator ξ)))
            weightedVolterraOperator_comp_adjoint.symm
        _ = weightedVolterraOperator
              (ContinuousLinearMap.adjoint weightedVolterraOperator
                (weightedPotentialOperator (weightedVolterraOperator ξ))) := rfl
        _ = weightedVolterraOperator ξ := by rw [← hrewrite]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (weightedBirmanSchwinger_fixed_mem_span _ hfixed)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    calc
      c • weightedVolterraScaleVector =
          ContinuousLinearMap.adjoint weightedVolterraOperator
            (weightedPotentialOperator (c • weightedScaleResonanceL2)) := by
        simp [weightedVolterraScaleVector, map_smul]
      _ = ContinuousLinearMap.adjoint weightedVolterraOperator
            (weightedPotentialOperator (weightedVolterraOperator ξ)) := by
        rw [hc]
      _ = ξ := hrewrite.symm
  · intro hξ
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hξ
    have hgen : weightedVolterraAPlus weightedVolterraScaleVector = 0 := by
      change weightedVolterraScaleVector -
        ContinuousLinearMap.adjoint weightedVolterraOperator
          (weightedPotentialOperator
            (weightedVolterraOperator weightedVolterraScaleVector)) = 0
      rw [weightedVolterra_scale_image]
      exact sub_self _
    change weightedVolterraAPlus ξ = 0
    rw [← hc, map_smul, hgen, smul_zero]

/-- Single environment asserting the explicit nonzero generator and exact
kernel, rather than hiding a target-shaped assumption. -/
theorem weightedVolterraAPlus_one_dimensional_kernel :
    weightedVolterraScaleVector ≠ 0 ∧
      weightedVolterraAPlus.ker =
        Submodule.span ℝ {weightedVolterraScaleVector} :=
  ⟨weightedVolterraScaleVector_ne_zero,
    weightedVolterraAPlus_kernel_eq_span⟩

end HBL.Modulation.Monopole
