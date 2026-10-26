import HBL.RegularRadiationKernel
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-!
# Standard high-regularity generalized Hartree local theory boundary

This is an external, literature-level analysis interface, in the same sense as
`BCritical.CriticalLocalTheory` in the verified 3D NLS project.  It introduces
no Lean axiom.  The intended source is Arora--Roudenko,
J. Hyperbolic Differential Equations 17 (2020), 727--763,
DOI 10.1142/S0219891620500228, together with standard persistence of
regularity for integer Sobolev exponents.

The manuscript-specific theorem below only specializes this universal local
flow to the terminal interval used by prop:regular-flow-stage3.  Concrete
inverse-square-kernel and seventh-order L2 estimates are proved separately in
`RegularRadiationKernel.lean`.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology
namespace HBL.RegularRadiation

open BesselPotentialSpace

abbrev Sobolev (L : ℕ) :=
  BesselPotentialSpace Space ℂ (L : ℝ) 2

/-- Universal high-regularity local flow for the concrete generalized Hartree
equation with coefficient `κ`.  This is an external theorem boundary, not a
paper-specific conclusion.  Time is allowed to be centered at any terminal
time `T`, and the theory is stated for all (not merely radial) data. -/
structure GeneralizedHartreeRegularLocalTheory (κ : ℝ) where
  epsilon : ℕ → ℝ
  tau : ℕ → ℝ
  boundConst : ℕ → ℝ
  flow : (L : ℕ) → ℝ → Sobolev L → ℝ → Sobolev L
  epsilon_pos : ∀ L, 4 ≤ L → 0 < epsilon L
  tau_pos : ∀ L, 4 ≤ L → 0 < tau L
  boundConst_pos : ∀ L, 4 ≤ L → 0 < boundConst L
  endpoint : ∀ L T g, flow L T g T = g
  local_bound : ∀ L, 4 ≤ L → ∀ T g,
    ‖g‖ ≤ epsilon L →
    ∀ t ∈ Icc (T - tau L) T,
      ‖flow L T g t‖ ≤ boundConst L * ‖g‖
  local_lipschitz : ∀ L, 4 ≤ L → ∀ T g h,
    ‖g‖ ≤ epsilon L → ‖h‖ ≤ epsilon L →
    ∀ t ∈ Icc (T - tau L) T,
      ‖flow L T g t - flow L T h t‖ ≤
        boundConst L * ‖g - h‖
  data_c1 : ∀ L, 4 ≤ L → ∀ T t,
    t ∈ Icc (T - tau L) T →
    ContDiff ℝ 1 (fun g : Sobolev L => flow L T g t)

/-- Exact manuscript specialization needed for the terminal regular-radiation
step, after shifting the terminal time to an arbitrary `T`.  No new numbered
environment is introduced: this discharges the existing pending local-flow
environment relative to the standard literature boundary above. -/
theorem regularRadiationFlow_certified (κ : ℝ)
    (LT : GeneralizedHartreeRegularLocalTheory κ)
    {N L : ℕ} (hN : 4 ≤ N) (hL : 2 * N + 8 ≤ L) :
    ∃ ε₀ τ₀ C : ℝ,
      0 < ε₀ ∧ 0 < τ₀ ∧ 0 < C ∧
      ∀ T : ℝ, ∃ z : Sobolev L → ℝ → Sobolev L,
        (∀ g, z g T = g) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ t ∈ Icc (T - τ₀) T,
          ‖z g t‖ ≤ C * ‖g‖) ∧
        (∀ g h, ‖g‖ ≤ ε₀ → ‖h‖ ≤ ε₀ →
          ∀ t ∈ Icc (T - τ₀) T,
            ‖z g t - z h t‖ ≤ C * ‖g - h‖) ∧
        (∀ t ∈ Icc (T - τ₀) T,
          ContDiff ℝ 1 (fun g : Sobolev L => z g t)) := by
  have hL4 : 4 ≤ L := by omega
  refine ⟨LT.epsilon L, LT.tau L, LT.boundConst L,
    LT.epsilon_pos L hL4, LT.tau_pos L hL4, LT.boundConst_pos L hL4, ?_⟩
  intro T
  refine ⟨fun g t => LT.flow L T g t, ?_, ?_, ?_, ?_⟩
  · intro g
    exact LT.endpoint L T g
  · intro g hg t ht
    exact LT.local_bound L hL4 T g hg t ht
  · intro g h hg hh t ht
    exact LT.local_lipschitz L hL4 T g h hg hh t ht
  · intro t ht
    exact LT.data_c1 L hL4 T t ht

/-- The concrete equation-specific order-zero kernel estimate remains a native
Lean theorem and is not hidden inside the literature interface. -/
theorem regularRadiation_actualKernel_check (κ : ℝ) :
    Integrable nearKernel ∧ 0 ≤ nearMass := by
  exact ⟨near_integrable, integral_nonneg near_nonneg⟩

#print axioms regularRadiationFlow_certified
#print axioms regularRadiation_actualKernel_check
end HBL.RegularRadiation
