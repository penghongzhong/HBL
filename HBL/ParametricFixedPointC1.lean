import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# C1 dependence of a uniformly contracting fixed point

This is a generic Banach-space calculus lemma used in the final HBL shooting
graph.  The only input is the standard C1 regularity of the joint map and
the strict contraction bound in the state variable.
-/

noncomputable section
set_option autoImplicit false

open scoped Topology ContDiff

namespace HBL.MainBackward

/-- A state derivative of norm < 1 makes I-D invertible. -/
theorem id_sub_isInvertible_of_norm_lt_one
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (D : X →L[ℝ] X) (hD : ‖D‖ < 1) :
    (ContinuousLinearMap.id ℝ X - D).IsInvertible := by
  have hu : IsUnit (1 - D) := isUnit_one_sub_of_norm_lt_one hD
  rcases hu with ⟨u, hu⟩
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ((↑(u⁻¹) : X →L[ℝ] X)))
  · ext x
    change ((1 - D) * (↑(u⁻¹) : X →L[ℝ] X)) x = x
    rw [← hu]
    simp
  · ext x
    change ((↑(u⁻¹) : X →L[ℝ] X) * (1 - D)) x = x
    rw [← hu]
    simp

/-- Local C1 implicit graph for a fixed-point equation, once the state
partial derivative is identified with I-D and ‖D‖<1. -/
theorem contracting_fixed_point_has_C1_local_graph
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : P × X → X) (p : P) (x : X)
    (D : X →L[ℝ] X)
    (hF : ContDiffAt ℝ 1 F (p,x))
    (hpartial :
      fderiv ℝ F (p,x) ∘L ContinuousLinearMap.inr ℝ P X =
        ContinuousLinearMap.id ℝ X - D)
    (hD : ‖D‖ < 1) :
    ∃ psi : P → X,
      psi p = x ∧
      ContDiffAt ℝ 1 psi p ∧
      ∀ᶠ y in 𝓝 p, F (y, psi y) = F (p,x) := by
  have hinv :
      (fderiv ℝ F (p,x) ∘L ContinuousLinearMap.inr ℝ P X).IsInvertible := by
    rw [hpartial]
    exact id_sub_isInvertible_of_norm_lt_one D hD
  let psi := hF.implicitFunction (by norm_num : (1 : ℕ∞ω) ≠ 0) hinv
  refine ⟨psi, ?_, ?_, ?_⟩
  · exact hF.implicitFunction_apply_self (by norm_num : (1 : ℕ∞ω) ≠ 0) hinv
  · exact hF.contDiffAt_implicitFunction (by norm_num : (1 : ℕ∞ω) ≠ 0) hinv
  · exact hF.eventually_apply_implicitFunction (by norm_num : (1 : ℕ∞ω) ≠ 0) hinv

/-- Direct C1 fixed-point graph theorem.  If x = Phi(p,x) and the
state derivative of Phi has norm strictly below one, then nearby parameters
have a C1 family of fixed points. -/
theorem parametric_contraction_fixed_point_C1
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (Phi : P × X → X) (p : P) (x : X)
    (D : X →L[ℝ] X)
    (hPhi : ContDiffAt ℝ 1 Phi (p,x))
    (hfix : Phi (p,x) = x)
    (hpartial :
      fderiv ℝ Phi (p,x) ∘L ContinuousLinearMap.inr ℝ P X = D)
    (hD : ‖D‖ < 1) :
    ∃ psi : P → X,
      psi p = x ∧
      ContDiffAt ℝ 1 psi p ∧
      ∀ᶠ y in 𝓝 p, psi y = Phi (y, psi y) := by
  let H : P × X → X := fun z => z.2 - Phi z
  have hH : ContDiffAt ℝ 1 H (p,x) := by
    exact contDiffAt_snd.sub hPhi
  have hHderiv :
      HasFDerivAt H
        (ContinuousLinearMap.snd ℝ P X - fderiv ℝ Phi (p,x))
        (p,x) := by
    exact hasFDerivAt_snd.sub ((hPhi.differentiableAt one_ne_zero).hasFDerivAt)
  have hpartialH :
      fderiv ℝ H (p,x) ∘L ContinuousLinearMap.inr ℝ P X =
        ContinuousLinearMap.id ℝ X - D := by
    rw [hHderiv.fderiv]
    ext v
    have hv := congrArg
      (fun T : X →L[ℝ] X => T v) hpartial
    change
      v - (fderiv ℝ Phi (p,x)) (0,v) = v - D v
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using congrArg (fun w : X => v - w) hv
  obtain ⟨psi, hpsi, hpsiC1, hsolve⟩ :=
    contracting_fixed_point_has_C1_local_graph
      H p x D hH hpartialH hD
  refine ⟨psi, hpsi, hpsiC1, ?_⟩
  have hH0 : H (p,x) = 0 := by
    dsimp [H]
    rw [hfix]
    exact sub_self x
  filter_upwards [hsolve] with y hy
  have hy0 : H (y, psi y) = 0 := by
    rw [hy, hH0]
  dsimp [H] at hy0
  exact sub_eq_zero.mp hy0

/-- Composition of a C1 shooting functional with a C1 fixed-point
graph remains C1. -/
theorem shootingFunctional_along_C1_fixedPoint
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Gamma : P × X → Y) (psi : P → X) (p : P)
    (hGamma : ContDiffAt ℝ 1 Gamma (p, psi p))
    (hpsi : ContDiffAt ℝ 1 psi p) :
    ContDiffAt ℝ 1 (fun y => Gamma (y, psi y)) p := by
  exact hGamma.comp p (contDiffAt_id.prodMk hpsi)

#print axioms id_sub_isInvertible_of_norm_lt_one
#print axioms contracting_fixed_point_has_C1_local_graph
#print axioms parametric_contraction_fixed_point_C1
#print axioms shootingFunctional_along_C1_fixedPoint

end HBL.MainBackward
