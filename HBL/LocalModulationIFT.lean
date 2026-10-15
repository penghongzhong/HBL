import HBL.ModulationJacobian
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum

/-!
Continuation of the first manuscript proof target: local dynamic modulation.

The manuscript computes the two parameter derivatives, obtains the normalized
Jacobian `-I₂`, and then invokes the finite-dimensional implicit-function
theorem.  This file formalizes exactly that last implication for a Banach
state space.  It does not introduce any later theorem from the manuscript.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

/-- The normalized parameter Jacobian occurring in the manuscript. -/
def parameterNegId : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  -(ContinuousLinearMap.id ℝ (ℝ × ℝ))

@[simp]
theorem parameterNegId_apply (p : ℝ × ℝ) :
    parameterNegId p = -p := by
  simp [parameterNegId]

/-- The normalized Jacobian is an isomorphism; its inverse is itself. -/
theorem parameterNegId_isInvertible : parameterNegId.IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (f := parameterNegId) (g := parameterNegId) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro p
    simp [parameterNegId]
  · apply ContinuousLinearMap.ext
    intro p
    simp [parameterNegId]

section TangentNormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalization of the two test functionals identifies the parameter
derivative computed in the preceding module with `-I₂`. -/
theorem tangentCoordinates_eq_parameterNegId
    (ellPlus ellMinus : E →L[ℝ] ℝ) (w z : E)
    (hPlus : ellPlus z = 1) (hMinus : ellMinus w = 1)
    (p : ℝ × ℝ) :
    tangentCoordinates ellPlus ellMinus w z p = parameterNegId p := by
  rw [tangentCoordinates_eq_neg ellPlus ellMinus w z hPlus hMinus p]
  simp

end TangentNormalization

section AbstractImplicitFunctionStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Formal version of the final sentence in the manuscript proof of the local
modulation lemma.

For a continuously differentiable constraint map on a Banach state space
times the two modulation parameters, if the constraint vanishes at the
standard bubble and the parameter derivative is the normalized matrix
`-I₂`, then there is a locally unique continuously differentiable parameter
selection solving the two orthogonality equations. -/
theorem local_modulation_from_normalized_jacobian
    (F : E × (ℝ × ℝ) → (ℝ × ℝ)) (u₀ : E)
    (hF0 : F (u₀, (0 : ℝ × ℝ)) = 0)
    (hC1 : ContDiffAt ℝ 1 F (u₀, (0 : ℝ × ℝ)))
    (hparam :
      fderiv ℝ F (u₀, (0 : ℝ × ℝ)) ∘L
          ContinuousLinearMap.inr ℝ E (ℝ × ℝ) = parameterNegId) :
    ∃ ψ : E → (ℝ × ℝ),
      ψ u₀ = 0 ∧
      ContDiffAt ℝ 1 ψ u₀ ∧
      (∀ᶠ u in 𝓝 u₀, F (u, ψ u) = 0) ∧
      (∀ᶠ v in 𝓝 (u₀, (0 : ℝ × ℝ)),
        (F v = 0 ↔ ψ v.1 = v.2)) := by
  have hInv :
      (fderiv ℝ F (u₀, (0 : ℝ × ℝ)) ∘L
          ContinuousLinearMap.inr ℝ E (ℝ × ℝ)).IsInvertible := by
    rw [hparam]
    exact parameterNegId_isInvertible
  let ψ : E → (ℝ × ℝ) := hC1.implicitFunction (by norm_num) hInv
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · dsimp [ψ]
    exact hC1.implicitFunction_apply_self (by norm_num) hInv
  · dsimp [ψ]
    exact hC1.contDiffAt_implicitFunction (by norm_num) hInv
  · have h := hC1.eventually_apply_implicitFunction (by norm_num) hInv
    filter_upwards [h] with u hu
    simpa [ψ, hF0] using hu
  · have h := hC1.eventually_apply_eq_iff_implicitFunction (by norm_num) hInv
    filter_upwards [h] with v hv
    simpa [ψ, hF0] using hv

end AbstractImplicitFunctionStep

end HBL.Modulation
