import HBL.ResidualTangentDerivative
import Mathlib.Tactic

/-!
# From weighted profile Lipschitz control to the retained feedback decay

The finite-profile environment gives local Lipschitz control of the residual
with its high-order time weight.  This file records the standard converse
mean-value step used by the main construction: at a differentiability point,
the same local Lipschitz constant bounds the Frechet derivative.  Combined
with the already verified residual-tangent identity, this supplies the
retained feedback coefficient E_theta without differentiating every profile
atom separately.
-/

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology

namespace HBL.MainBackward

/-- Local weighted Lipschitz control of the residual bounds its Frechet
derivative by the same time weight. -/
theorem residual_derivative_bound_from_local_lipschitz
    {Y X : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (R : Y → X) (theta : Y) (Rprime : Y →L[ℝ] X)
    (s C nu : ℝ)
    (hs : 0 < s) (hC : 0 ≤ C)
    (hR : HasFDerivAt R Rprime theta)
    (hLip : ∀ᶠ eta in 𝓝 theta,
      ‖R eta - R theta‖ ≤ (C * s ^ (-nu)) * ‖eta - theta‖) :
    ‖Rprime‖ ≤ C * s ^ (-nu) := by
  have hcoef : 0 ≤ C * s ^ (-nu) :=
    mul_nonneg hC (Real.rpow_nonneg hs.le _)
  exact hR.le_of_lip' hcoef hLip

/-- In the retained-feedback notation E=-D_theta R, the same bound holds
with no loss and no sign ambiguity. -/
theorem retained_feedback_coefficient_bound_from_residual
    {Y X : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (R : Y → X) (theta : Y) (E Rprime : Y →L[ℝ] X)
    (s C nu : ℝ)
    (hs : 0 < s) (hC : 0 ≤ C)
    (hR : HasFDerivAt R Rprime theta)
    (hE : E = -Rprime)
    (hLip : ∀ᶠ eta in 𝓝 theta,
      ‖R eta - R theta‖ ≤ (C * s ^ (-nu)) * ‖eta - theta‖) :
    ‖E‖ ≤ C * s ^ (-nu) := by
  rw [hE, norm_neg]
  exact residual_derivative_bound_from_local_lipschitz
    R theta Rprime s C nu hs hC hR hLip

/-- An arbitrarily high fixed profile order can be chosen above the
feedback threshold nu>2. -/
theorem exists_feedback_decay_exponent
    (N : ℝ) (hN : 3 < N) :
    ∃ nu : ℝ, 2 < nu ∧ nu < N := by
  refine ⟨(N + 2) / 2, ?_, ?_⟩ <;> linarith

#print axioms residual_derivative_bound_from_local_lipschitz
#print axioms retained_feedback_coefficient_bound_from_residual
#print axioms exists_feedback_decay_exponent

end HBL.MainBackward
