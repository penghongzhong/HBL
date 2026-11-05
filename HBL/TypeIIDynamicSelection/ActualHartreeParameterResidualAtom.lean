import HBL.FiniteProfileResidualLedger
import HBL.TypeIIDynamicSelection.ActualMonopoleParameterSpeedGain
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/-!
# The genuine two threshold coordinates as a realized residual atom

For the asymptotic ledger we extend the physical coordinate pair by zero at
the single endpoint s=1.  On every s>1 the value is exactly the actual plus
and minus threshold coordinate of the monopole effective increment.

The order 1+actualMonopoleParameterGain is proved by the existing physical
projection theorem, not assigned through GainCause.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.ResidualLedger

def actualHartreeParameterResidualValue
    (c b omega : ℝ → ℝ) (s : ℝ) : ℝ × ℝ :=
  if 1 < s then
    (monopoleThresholdCoordinatePlus c b omega s,
      monopoleThresholdCoordinateMinus c b omega s)
  else (0, 0)

/-- The actual two-dimensional threshold-coordinate residual is a realized
atom of order 1+delta_parameter. -/
theorem actual_Hartree_parameter_realized_atom
    (c b omega : ℝ → ℝ) (beta A : ℝ)
    (hbeta : 1 / 2 < beta) (hA : 0 ≤ A)
    (hc : Differentiable ℝ c) (hb : Measurable b) (homega : Measurable omega)
    (hsmall : ∀ s : ℝ, 1 < s → |c s| ≤ 1)
    (hdecay : ∀ s : ℝ, 1 < s →
      |c s| ≤ A * s ^ (-beta) ∧
      |deriv c s| ≤ A * s ^ (-1 - beta) ∧
      |b s| ≤ A * s ^ (-1 : ℝ) ∧
      |omega s| ≤ A * s ^ (-1 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∃ atom : WeightedResidualAtom (ℝ × ℝ),
        atom.value = actualHartreeParameterResidualValue c b omega ∧
        atom.order = 1 + actualMonopoleParameterGain beta ∧
        atom.constant = C * (A + A ^ 2) := by
  obtain ⟨C, hC, hBound⟩ :=
    actual_monopole_threshold_coordinate_speed_gain
  have hConst : 0 ≤ C * (A + A ^ 2) := by
    have hAsum : 0 ≤ A + A ^ 2 := add_nonneg hA (sq_nonneg A)
    exact mul_nonneg hC.le hAsum
  let atom : WeightedResidualAtom (ℝ × ℝ) :=
    { value := actualHartreeParameterResidualValue c b omega
      order := 1 + actualMonopoleParameterGain beta
      constant := C * (A + A ^ 2)
      constant_nonneg := hConst
      bound := by
        intro s hs
        by_cases h1 : 1 < s
        · have hcoord :=
            hBound (c := c) (b := b) (omega := omega)
              (s0 := 1) (beta := beta) (A := A)
              (by norm_num) hbeta hA hc hb homega hsmall hdecay s h1
          have hp :
              |monopoleThresholdCoordinatePlus c b omega s| ≤
                C * (A + A ^ 2) *
                  s ^ (-1 - actualMonopoleParameterGain beta) :=
            (le_add_of_nonneg_right
              (abs_nonneg (monopoleThresholdCoordinateMinus c b omega s))).trans
              hcoord
          have hm :
              |monopoleThresholdCoordinateMinus c b omega s| ≤
                C * (A + A ^ 2) *
                  s ^ (-1 - actualMonopoleParameterGain beta) :=
            (le_add_of_nonneg_left
              (abs_nonneg (monopoleThresholdCoordinatePlus c b omega s))).trans
              hcoord
          rw [actualHartreeParameterResidualValue, if_pos h1, Prod.norm_mk,
            Real.norm_eq_abs, Real.norm_eq_abs]
          have hmax := max_le hp hm
          simpa only [show -(1 + actualMonopoleParameterGain beta) =
              -1 - actualMonopoleParameterGain beta by ring] using hmax
        · have hs1 : s = 1 := by linarith
          subst s
          simp [actualHartreeParameterResidualValue, hConst] }
  exact ⟨C, hC, atom, rfl, rfl, rfl⟩

theorem actual_Hartree_parameter_realized_gain_positive
    (beta : ℝ) (hbeta : 1 / 2 < beta) :
    1 < 1 + actualMonopoleParameterGain beta := by
  have h := actual_monopole_parameter_gain_positive beta hbeta
  linarith

end HBL.TypeIIDynamicSelection
