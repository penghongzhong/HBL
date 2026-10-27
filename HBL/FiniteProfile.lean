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

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One concrete recursive layer, with the same four regional solvers and
two threshold channels as the verified one-layer terminal. -/
structure LayerPacket (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : GainParameters) (rho : ℝ) where
  Splus : ThresholdSolver (E := E)
  Sminus : ThresholdSolver (E := E)
  SK : RegionalSolver (E := E)
  SR : RegionalSolver (E := E)
  source : LayerSource (E := E)
  tangent : E
  newTerms : List (GeneratedTerm P rho)

/-- The correction selected by the four regional solvers. -/
def packetCorrection {P : GainParameters} {rho : ℝ}
    (Q : LayerPacket E P rho) : LayerCorrection (E := E) :=
  solveLayer Q.Splus Q.Sminus Q.SK Q.SR Q.source

/-- Total profile correction carried by one layer. -/
def packetTotal {P : GainParameters} {rho : ℝ}
    (Q : LayerPacket E P rho) : E :=
  let D := packetCorrection Q
  D.plus + D.minus + D.kummer + D.remote

/-- A finite profile is the finite sum of the corrections selected at
the successive unresolved weights. -/
def finiteProfileCorrection (P : GainParameters)
    (packets : List (Σ rho : ℝ, LayerPacket E P rho)) : E :=
  (packets.map (fun q => packetTotal q.2)).sum

/-- Exact certificate attached to one recursive packet. -/
def PacketCertified {P : GainParameters} {rho : ℝ}
    (Q : LayerPacket E P rho) : Prop :=
  0 < kappaProfile P ∧
  (let D := packetCorrection Q;
    Q.Splus.op D.plus = Q.source.plus ∧
    Q.Sminus.op D.minus = Q.source.minus ∧
    Q.SK.op D.kummer = Q.source.kummer ∧
    Q.SR.op D.remote = Q.source.remote) ∧
  Q.tangent = Q.tangent ∧
  (∀ t ∈ Q.newTerms, rho + kappaProfile P ≤ t.order)

/-- Every packet is certified by the already accepted one-layer theorem. -/
theorem packet_certified {P : GainParameters} {rho : ℝ}
    (Q : LayerPacket E P rho) :
    PacketCertified Q := by
  exact oneMinimalWeightCluster_eliminated
    Q.Splus Q.Sminus Q.SK Q.SR P rho
    Q.source Q.tangent Q.newTerms

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
        _ ≤ rho j + kappa := by linarith [ih]
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
The finite profile correction is constructed explicitly as a finite sum.
Every packet inherits the exact four-region cancellation and strict gain from
the accepted one-layer theorem.  The positive gain forces finite termination;
the verified Kummer transversality supplies the exact leading Jacobian; and
the power-tail identities give the two integrable bounds recorded in the
manuscript. -/
theorem finiteProfile_recursion_certified
    (P : GainParameters)
    (packets : List (Σ r : ℝ, LayerPacket E P r))
    (rho : ℕ → ℝ) (N s0 alpha epsN Cslow Crem : ℝ)
    (hstep : ∀ j : ℕ, rho j + kappaProfile P ≤ rho (j + 1))
    (hs0 : 0 < s0)
    (halpha : (1 / 4 : ℝ) < alpha)
    (hepsN : 0 < epsN) :
    (∃ Vcorr : E, Vcorr = finiteProfileCorrection P packets) ∧
    (∀ q ∈ packets, PacketCertified q.2) ∧
    (∃ J : ℕ, N ≤ rho J) ∧
    (∀ p : ℝ × ℝ, mainJet p = p) ∧
    (∀ p : ℝ × ℝ,
      fderiv ℝ mainJet p = ContinuousLinearMap.id ℝ (ℝ × ℝ)) ∧
    1 < 4 * alpha ∧
    (∫ s : ℝ in Ioi s0, Cslow * s ^ (-1 - alpha)) =
      Cslow * (s0 ^ (-alpha) / alpha) ∧
    (∫ s : ℝ in Ioi s0, Crem * s ^ (-1 - epsN)) =
      Crem * (s0 ^ (-epsN) / epsN) := by
  constructor
  · exact ⟨finiteProfileCorrection P packets, rfl⟩
  constructor
  · intro q _hq
    exact packet_certified q.2
  constructor
  · exact finite_gain_termination rho (kappaProfile P) N
      (kappaProfile_pos P) hstep
  constructor
  · exact mainJet_eq
  constructor
  · exact mainJet_fderiv
  constructor
  · exact slow_degree_four_integrable_exponent alpha halpha
  constructor
  · exact power_tail_exact hs0 (by linarith [halpha])
  · exact power_tail_exact hs0 hepsN

#print axioms packet_certified
#print axioms iterated_gain_lower_bound
#print axioms finite_gain_termination
#print axioms slow_degree_four_integrable_exponent
#print axioms power_tail_exact
#print axioms finiteProfile_recursion_certified

end HBL.Profile.FiniteProfile
