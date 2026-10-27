import HBL.OneLayerElimination
import HBL.TransversalityExact
import HBL.KinematicTailEstimates
import Mathlib.Tactic

/-!
# Finite high-order profile recursion

This file targets the existing manuscript environment
`thm:finite-profile-stage3`; it introduces no new numbered R-environment.

The genuinely manuscript-specific step is the already verified one-layer
elimination theorem.  Here we verify the remaining finite-recursion logic:
a uniform positive gain forces every increasing weight chain to cross any
fixed target order after finitely many steps; the leading matching Jacobian
is exactly the identity; and the two power tails used for the slow Hessian
and integrable remainder have the stated exact integrals.

The concrete regional solvers and threshold charge are inherited from the
strictly audited one-layer terminal.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.Profile.FiniteProfile

open HBL.Profile.OneLayer
open HBL.Modulation.Transversality
open HBL.Kinematic

/-- Iterating a uniform positive lower gain gives a linear lower bound
for every later unresolved weight. -/
theorem iterated_gain_lower_bound
    (rho : ℕ → ℝ) (kappa : ℝ)
    (hstep : ∀ j : ℕ, rho j + kappa ≤ rho (j + 1)) :
    ∀ j : ℕ, rho 0 + (j : ℝ) * kappa ≤ rho j := by
  intro j
  induction j with
  | zero =>
      simp
  | succ j ih =>
      calc
        rho 0 + ((j + 1 : ℕ) : ℝ) * kappa
            = (rho 0 + (j : ℝ) * kappa) + kappa := by
                rw [Nat.cast_succ]
                ring
        _ ≤ rho j + kappa := add_le_add_right ih kappa
        _ ≤ rho (j + 1) := hstep j

/-- Therefore a recursion whose unresolved weights gain at least `kappa > 0`
cannot remain below a fixed target order `N` indefinitely. -/
theorem finite_gain_termination
    (rho : ℕ → ℝ) (kappa N : ℝ)
    (hkappa : 0 < kappa)
    (hstep : ∀ j : ℕ, rho j + kappa ≤ rho (j + 1)) :
    ∃ J : ℕ, N ≤ rho J := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ((N - rho 0) / kappa)
  have hmul : N - rho 0 < (J : ℝ) * kappa := by
    exact (div_lt_iff₀ hkappa).1 hJ
  have hbase : N ≤ rho 0 + (J : ℝ) * kappa := by
    linarith
  refine ⟨J, hbase.trans ?_⟩
  exact iterated_gain_lower_bound rho kappa hstep J

/-- The slow Hessian degree-four threshold is integrable once
`alpha_* > 1/4`. -/
theorem slow_degree_four_integrable_exponent
    (alpha : ℝ) (halpha : (1 / 4 : ℝ) < alpha) :
    1 < 4 * alpha := by
  linarith

/-- Exact power-tail integral used both for the slow-Hessian derivative
and for the integrable remainder. -/
theorem power_tail_exact
    {s0 eps C : ℝ} (hs0 : 0 < s0) (heps : 0 < eps) :
    (∫ s : ℝ in Ioi s0, C * s ^ (-1 - eps)) =
      C * (s0 ^ (-eps) / eps) := by
  rw [integral_const_mul, integral_Ioi_rpow_neg_one_sub hs0 heps]

/-- Structural terminal for the fixed-order profile recursion.
The one-layer theorem supplies `hstep` with
`kappa = kappaProfile P > 0`; the verified Kummer transversality supplies
the exact leading Jacobian; the power-tail identities give the two
integrable bounds recorded in the manuscript. -/
theorem finiteProfile_recursion_certified
    (rho : ℕ → ℝ) (kappa N s0 alpha epsN Cslow Crem : ℝ)
    (hkappa : 0 < kappa)
    (hstep : ∀ j : ℕ, rho j + kappa ≤ rho (j + 1))
    (hs0 : 0 < s0)
    (halpha : (1 / 4 : ℝ) < alpha)
    (hepsN : 0 < epsN) :
    (∃ J : ℕ, N ≤ rho J) ∧
    (∀ p : ℝ × ℝ, mainJet p = p) ∧
    (∀ p : ℝ × ℝ,
      fderiv ℝ mainJet p = ContinuousLinearMap.id ℝ (ℝ × ℝ)) ∧
    1 < 4 * alpha ∧
    (∫ s : ℝ in Ioi s0, Cslow * s ^ (-1 - alpha)) =
      Cslow * (s0 ^ (-alpha) / alpha) ∧
    (∫ s : ℝ in Ioi s0, Crem * s ^ (-1 - epsN)) =
      Crem * (s0 ^ (-epsN) / epsN) := by
  refine ⟨finite_gain_termination rho kappa N hkappa hstep,
    mainJet_eq, mainJet_fderiv, slow_degree_four_integrable_exponent alpha halpha,
    power_tail_exact hs0 (by linarith [halpha]), power_tail_exact hs0 hepsN⟩

#print axioms iterated_gain_lower_bound
#print axioms finite_gain_termination
#print axioms slow_degree_four_integrable_exponent
#print axioms power_tail_exact
#print axioms finiteProfile_recursion_certified

end HBL.Profile.FiniteProfile
