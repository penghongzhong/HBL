import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Tactic

/-!
# Remote block perturbation inverse

This is the Banach--Neumann step used in the manuscript formula
  L_varpi^{-1} = (I + G_free H_varpi)^{-1} G_free.
Unlike the previous structural one-layer package, the perturbative inverse
below is constructed inside Lean. The only remaining remote-region input is
therefore the explicit free inverse for the three frozen phase/log blocks.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Profile.Remote

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def perturbationBlock
    (G H : E →L[ℝ] E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + G ∘L H

theorem perturbationBlock_isInvertible
    (G H : E →L[ℝ] E)
    (hsmall : ‖G ∘L H‖ ≤ (1 / 2 : ℝ)) :
    (perturbationBlock G H).IsInvertible := by
  let K : E →L[ℝ] E := G ∘L H
  have hK : ‖K‖ < 1 := by
    dsimp [K]
    linarith
  have hneg : ‖-K‖ < 1 := by simpa using hK
  have hu0 : IsUnit (1 - (-K) : E →L[ℝ] E) :=
    NormedRing.IsUnit.one_sub_of_norm_lt_one hneg
  have heq : (1 - (-K) : E →L[ℝ] E) = perturbationBlock G H := by
    unfold perturbationBlock
    dsimp [K]
    abel
  rw [heq] at hu0
  rcases hu0 with ⟨u, hu⟩
  refine ⟨ContinuousLinearEquiv.unitsEquiv ℝ E u, ?_⟩
  ext x
  rw [ContinuousLinearEquiv.unitsEquiv_apply]
  exact congrArg (fun T : E →L[ℝ] E => T x) hu

def perturbedInverse
    (G H : E →L[ℝ] E) : E →L[ℝ] E :=
  (perturbationBlock G H).inverse ∘L G

theorem free_factorization_right
    (L G H : E →L[ℝ] E)
    (hLG : L ∘L G = ContinuousLinearMap.id ℝ E) :
    ∀ x : E,
      L (perturbationBlock G H x) = (L + H) x := by
  intro x
  unfold perturbationBlock
  simp only [add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_add]
  have h := congrArg (fun T : E →L[ℝ] E => T (H x)) hLG
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    congrArg (fun y : E => L x + y) h

theorem free_factorization_left
    (L G H : E →L[ℝ] E)
    (hGL : G ∘L L = ContinuousLinearMap.id ℝ E) :
    ∀ x : E,
      G ((L + H) x) = perturbationBlock G H x := by
  intro x
  unfold perturbationBlock
  simp only [add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_add]
  have h := congrArg (fun T : E →L[ℝ] E => T x) hGL
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    congrArg (fun y : E => y + G (H x)) h

theorem perturbedInverse_right
    (L G H : E →L[ℝ] E)
    (hLG : L ∘L G = ContinuousLinearMap.id ℝ E)
    (hsmall : ‖G ∘L H‖ ≤ (1 / 2 : ℝ)) :
    ∀ f : E, (L + H) (perturbedInverse G H f) = f := by
  intro f
  have hB := perturbationBlock_isInvertible G H hsmall
  let y := (perturbationBlock G H).inverse (G f)
  have hfac := free_factorization_right L G H hLG y
  have hBy : perturbationBlock G H y = G f := by
    dsimp [y]
    exact hB.self_apply_inverse (G f)
  unfold perturbedInverse
  simp only [ContinuousLinearMap.comp_apply]
  change (L + H) y = f
  rw [← hfac, hBy]
  have h := congrArg (fun T : E →L[ℝ] E => T f) hLG
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

theorem perturbedInverse_left
    (L G H : E →L[ℝ] E)
    (hGL : G ∘L L = ContinuousLinearMap.id ℝ E)
    (hsmall : ‖G ∘L H‖ ≤ (1 / 2 : ℝ)) :
    ∀ x : E, perturbedInverse G H ((L + H) x) = x := by
  intro x
  have hB := perturbationBlock_isInvertible G H hsmall
  have hfac := free_factorization_left L G H hGL x
  unfold perturbedInverse
  simp only [ContinuousLinearMap.comp_apply]
  rw [hfac]
  exact hB.inverse_apply_self x

theorem perturbedBlock_bijective
    (L G H : E →L[ℝ] E)
    (hLG : L ∘L G = ContinuousLinearMap.id ℝ E)
    (hGL : G ∘L L = ContinuousLinearMap.id ℝ E)
    (hsmall : ‖G ∘L H‖ ≤ (1 / 2 : ℝ)) :
    Function.Bijective (L + H) := by
  constructor
  · intro x y hxy
    have hx := perturbedInverse_left L G H hGL hsmall x
    have hy := perturbedInverse_left L G H hGL hsmall y
    rw [hxy] at hx
    exact hx.symm.trans hy
  · intro f
    exact ⟨perturbedInverse G H f,
      perturbedInverse_right L G H hLG hsmall f⟩

theorem perturbedBlock_unique_solution
    (L G H : E →L[ℝ] E)
    (hLG : L ∘L G = ContinuousLinearMap.id ℝ E)
    (hGL : G ∘L L = ContinuousLinearMap.id ℝ E)
    (hsmall : ‖G ∘L H‖ ≤ (1 / 2 : ℝ))
    (f : E) :
    ∃! x : E, (L + H) x = f := by
  refine ⟨perturbedInverse G H f,
    perturbedInverse_right L G H hLG hsmall f, ?_⟩
  intro x hx
  exact (perturbedBlock_bijective L G H hLG hGL hsmall).1
    (hx.trans (perturbedInverse_right L G H hLG hsmall f).symm)

#print axioms perturbationBlock_isInvertible
#print axioms perturbedInverse_right
#print axioms perturbedInverse_left
#print axioms perturbedBlock_bijective
#print axioms perturbedBlock_unique_solution

end HBL.Profile.Remote
