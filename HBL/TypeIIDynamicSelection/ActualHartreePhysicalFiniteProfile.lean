import HBL.FiniteProfile
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalOneLayerGain
import Mathlib.Tactic

/-!
# Finite profile recursion with the physical Hartree gain minimum

This is the finite-recursion consumer of the physical one-layer gain theorem.
The old structural Frobenius half-order is not used: termination is driven by
the actual physical kappa, whose fifth entry is the true Kummer tail gain
3*beta/128.

The theorem is still conditional on an honest sequence of physical layer
packets and on the step relation for the unresolved weights. Constructing
those packets from the exact new Hartree PDE residual is the remaining
source-classification bridge; this file does not hide that obligation.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Profile.OneLayer
open HBL.Profile.FiniteProfile
open HBL.Modulation.Transversality
open HBL.Kinematic

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

structure ActualHartreeLayerPacket
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (beta rho base : ℝ) where
  Splus : ThresholdSolver (E := E)
  Sminus : ThresholdSolver (E := E)
  SK : RegionalSolver (E := E)
  SR : RegionalSolver (E := E)
  source : LayerSource (E := E)
  tangent : E
  newTerms : List (ActualHartreeGeneratedTerm beta rho base)

def actualHartreePacketCorrection
    {beta rho base : ℝ}
    (Q : ActualHartreeLayerPacket E beta rho base) :
    LayerCorrection (E := E) :=
  solveLayer Q.Splus Q.Sminus Q.SK Q.SR Q.source

def actualHartreePacketTotal
    {beta rho base : ℝ}
    (Q : ActualHartreeLayerPacket E beta rho base) : E :=
  let D := actualHartreePacketCorrection Q
  D.plus + D.minus + D.kummer + D.remote

def actualHartreeFiniteProfileCorrection
    (beta rho : ℝ)
    (packets : List (Σ base : ℝ, ActualHartreeLayerPacket E beta rho base)) : E :=
  (packets.map (fun q => actualHartreePacketTotal q.2)).sum

def ActualHartreePacketCertified
    {beta rho base : ℝ}
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4)
    (Q : ActualHartreeLayerPacket E beta rho base) : Prop :=
  0 < actualHartreePhysicalKappa beta rho ∧
  (let D := actualHartreePacketCorrection Q;
    Q.Splus.op D.plus = Q.source.plus ∧
    Q.Sminus.op D.minus = Q.source.minus ∧
    Q.SK.op D.kummer = Q.source.kummer ∧
    Q.SR.op D.remote = Q.source.remote) ∧
  Q.tangent = Q.tangent ∧
  (∀ t ∈ Q.newTerms,
    base + actualHartreePhysicalKappa beta rho ≤ t.order)

theorem actual_Hartree_packet_certified
    {beta rho base : ℝ}
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4)
    (Q : ActualHartreeLayerPacket E beta rho base) :
    ActualHartreePacketCertified hbeta hrho hflat Q := by
  exact actual_Hartree_oneMinimalWeightCluster_eliminated
    Q.Splus Q.Sminus Q.SK Q.SR
    beta rho base hbeta hrho hflat
    Q.source Q.tangent Q.newTerms

theorem actual_Hartree_physical_gain_finite_termination
    (beta rho : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4)
    (weight : ℕ → ℝ) (N : ℝ)
    (hstep : ∀ j : ℕ,
      weight j + actualHartreePhysicalKappa beta rho ≤ weight (j + 1)) :
    ∃ J : ℕ, N ≤ weight J := by
  exact finite_gain_termination weight
    (actualHartreePhysicalKappa beta rho) N
    (actual_Hartree_physical_kappa_positive beta rho hbeta hrho hflat)
    hstep

theorem actual_Hartree_finiteProfile_recursion_certified
    (beta rho : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4)
    (packets : List
      (Σ base : ℝ, ActualHartreeLayerPacket E beta rho base))
    (weight : ℕ → ℝ) (N s0 alpha epsN Cslow Crem : ℝ)
    (hstep : ∀ j : ℕ,
      weight j + actualHartreePhysicalKappa beta rho ≤ weight (j + 1))
    (hs0 : 0 < s0)
    (halpha : (1 / 4 : ℝ) < alpha)
    (hepsN : 0 < epsN) :
    (∃ Vcorr : E,
      Vcorr = actualHartreeFiniteProfileCorrection beta rho packets) ∧
    (∀ q ∈ packets,
      ActualHartreePacketCertified hbeta hrho hflat q.2) ∧
    (∃ J : ℕ, N ≤ weight J) ∧
    (∀ p : ℝ × ℝ, mainJet p = p) ∧
    (∀ p : ℝ × ℝ,
      fderiv ℝ mainJet p = ContinuousLinearMap.id ℝ (ℝ × ℝ)) ∧
    1 < 4 * alpha ∧
    (∫ s : ℝ in Ioi s0, Cslow * s ^ (-1 - alpha)) =
      Cslow * (s0 ^ (-alpha) / alpha) ∧
    (∫ s : ℝ in Ioi s0, Crem * s ^ (-1 - epsN)) =
      Crem * (s0 ^ (-epsN) / epsN) := by
  constructor
  · exact ⟨actualHartreeFiniteProfileCorrection beta rho packets, rfl⟩
  constructor
  · intro q _hq
    exact actual_Hartree_packet_certified hbeta hrho hflat q.2
  constructor
  · exact actual_Hartree_physical_gain_finite_termination
      beta rho hbeta hrho hflat weight N hstep
  constructor
  · exact mainJet_eq
  constructor
  · exact mainJet_fderiv
  constructor
  · exact slow_degree_four_integrable_exponent alpha halpha
  constructor
  · exact power_tail_exact hs0 (by linarith [halpha])
  · exact power_tail_exact hs0 hepsN

end HBL.TypeIIDynamicSelection
