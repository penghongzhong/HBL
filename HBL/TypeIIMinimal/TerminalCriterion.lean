import HBL.BlowupNonextension
import HBL.MainRateSelection
import Mathlib.Tactic

/-!
# Genuine Type II: the terminal consequences

This block is NOT a PDE existence theorem. It verifies the part of the
revised Hartree main theorem that deduces bounded critical norm and failure
of strong continuation from an actual concentration decomposition and
separation of the rescaled physical bubble.

A radial PDE orbit, its Hartree identity, and actual scale separation of
W_lambda remain separate, indispensable mathematical obligations.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace HBL.TypeIIMinimal

/-- Fixing the nonresonant speed nu = sqrt 2 retains the original parameter
restriction from the historical HBL main theorem. -/
theorem chosen_mu_above_sobolev_threshold :
    (9 / 16 : ℝ) < Real.sqrt 2 / 2 := by
  have hroot : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

theorem chosen_nu_above_one :
    (1 : ℝ) < Real.sqrt 2 := by
  have hroot : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- The original dynamical-rate formula gives the fixed nonresonant rate. -/
theorem chosen_physical_concentration_rate :
    HBL.MainBackward.selectedPhysicalRate (Real.sqrt 2 / 2) =
      1 / 2 + Real.sqrt 2 := by
  unfold HBL.MainBackward.selectedPhysicalRate
  ring

/-- Positive terminal mu makes the physical rate faster than self-similar. -/
theorem positive_mu_is_super_self_similar {mu : ℝ} (hmu : 0 < mu) :
    (1 / 2 : ℝ) < HBL.MainBackward.selectedPhysicalRate mu := by
  unfold HBL.MainBackward.selectedPhysicalRate
  linarith

/-- A nonvanishing concentrating profile and an asymptotically fixed
remainder give bounded critical norm and no strong continuation.
Separation remains a separately provable input for the physical Hartree
bubble, not a new axiom. The true PDE solution is not constructed here. -/
theorem critical_norm_bounded_and_no_strong_terminal_limit
    {X : Type*} [NormedAddCommGroup X]
    (u bubble : ℕ → X) (etaT : X)
    (M E : ℝ)
    (hbubble : ∀ n : ℕ, ‖bubble n‖ ≤ M)
    (herror : ∀ n : ℕ, ‖u n - (bubble n + etaT)‖ ≤ E)
    (herror_tends_zero :
      Tendsto (fun n : ℕ => dist (u n) (bubble n + etaT))
        atTop (𝓝 (0 : ℝ)))
    (hscale_separation : ∃ eps : ℝ, 0 < eps ∧
      ∀ N : ℕ, ∃ m ≥ N, ∃ n ≥ N, eps ≤ dist (bubble m) (bubble n)) :
    (∀ n : ℕ, ‖u n‖ ≤ M + ‖etaT‖ + E) ∧
      (∀ limit : X, ¬ Tendsto u atTop (𝓝 limit)) := by
  constructor
  · intro n
    have hdecomp :
        ‖u n‖ ≤ ‖u n - (bubble n + etaT)‖ + ‖bubble n + etaT‖ := by
      have h := norm_add_le (u n - (bubble n + etaT)) (bubble n + etaT)
      simpa only [sub_add_cancel] using h
    have hb := norm_add_le (bubble n) etaT
    linarith [hdecomp, herror n, hbubble n, hb]
  · exact HBL.MainBackward.no_strong_limit_of_separated_profile
      u bubble etaT herror_tends_zero hscale_separation

end HBL.TypeIIMinimal
