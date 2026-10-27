import HBL.FiniteProfileResidualLedger
import HBL.ResidualDecayFromLipschitz

/-!
# Retained feedback from the finite-profile atom ledger

This closes the bookkeeping gap between the accepted fixed-order profile
recursion and the retained threshold feedback.  Once the residual is the
finite sum of realized generated atoms of order at least N, its Frechet
parameter derivative has exactly the same s^{-N} bound.
-/

noncomputable section

open Filter
open scoped Topology
set_option autoImplicit false

namespace HBL.MainBackward

open HBL.Profile.ResidualLedger

theorem retained_feedback_bound_from_finite_atoms
    {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (atoms : List (ParametricResidualAtom P E))
    (N s : ℝ) (theta : P)
    (hN : ∀ a ∈ atoms, N ≤ a.order)
    (hs : 1 ≤ s)
    (Rprime Etheta : P →L[ℝ] E)
    (hR : HasFDerivAt
      (fun eta : P => parametricResidualSum atoms eta s)
      Rprime theta)
    (hE : Etheta = -Rprime) :
    ‖Etheta‖ ≤ parametricResidualConstant atoms * s ^ (-N) := by
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hC : 0 ≤ parametricResidualConstant atoms :=
    parametricResidualConstant_nonneg atoms
  have hLip :
      ∀ᶠ eta in 𝓝 theta,
        ‖parametricResidualSum atoms eta s -
            parametricResidualSum atoms theta s‖ ≤
          (parametricResidualConstant atoms * s ^ (-N)) *
            ‖eta - theta‖ :=
    parametricResidualSum_eventually_lipschitz atoms N s theta hN hs
  exact retained_feedback_coefficient_bound_from_residual
    (fun eta : P => parametricResidualSum atoms eta s)
    theta Etheta Rprime s
    (parametricResidualConstant atoms) N
    hspos hC hR hE hLip

/-- Choosing profile order N>2 gives precisely the decay exponent needed by
the one-power-loss retained-threshold feedback mechanism. -/
theorem finite_atoms_supply_feedback_exponent
    {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (atoms : List (ParametricResidualAtom P E))
    (N s : ℝ) (theta : P)
    (hN2 : 2 < N)
    (horder : ∀ a ∈ atoms, N ≤ a.order)
    (hs : 1 ≤ s)
    (Rprime Etheta : P →L[ℝ] E)
    (hR : HasFDerivAt
      (fun eta : P => parametricResidualSum atoms eta s)
      Rprime theta)
    (hE : Etheta = -Rprime) :
    2 < N ∧
      ‖Etheta‖ ≤ parametricResidualConstant atoms * s ^ (-N) := by
  exact ⟨hN2,
    retained_feedback_bound_from_finite_atoms
      atoms N s theta horder hs Rprime Etheta hR hE⟩

#print axioms retained_feedback_bound_from_finite_atoms
#print axioms finite_atoms_supply_feedback_exponent

end HBL.MainBackward
