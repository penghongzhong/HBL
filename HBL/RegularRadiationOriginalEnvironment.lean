import HBL.RegularRadiationFlow
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Exact original terminal regular-radiation environment

This file keeps the standard high-regularity generalized Hartree local theory
as an explicit literature boundary. It adds no axiom and does not pretend to
reprove the Strichartz fixed-point theorem. Relative to that boundary it
verifies every clause used in manuscript `prop:regular-flow-stage3`:
endpoint data, the actual Hartree equation, strong time derivative,
uniqueness, radiality, the high Sobolev bound, all finite time jets, and C1
dependence into a genuine normed path space.

For the basic local well-posedness input see Arora--Roudenko, JHDE 17 (2020),
Theorem 1.1 / Theorem 3.1 (arXiv:1910.01085), specialized to N=3, b=2,
p=4. The standard persistence-of-regularity upgrade, finite jets and C1
parameter statement are intentionally visible as fields of the literature
interface rather than hidden in the Lean proof.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.RegularRadiation

/-- Fixed compact parameter interval used to encode a terminal time window. -/
abbrev UnitTime := Icc (0 : ℝ) 1

/-- Normed path space for the C1 dependence assertion. -/
abbrev RegularRadiationPath (L : ℕ) :=
  BoundedContinuousFunction UnitTime (Sobolev L)

/-- Affine parametrization of `[T-tau,T]` by `UnitTime`. -/
def terminalAffineTime (T τ : ℝ) (σ : UnitTime) : ℝ :=
  T - τ + τ * (σ : ℝ)

/-- A strong regular solution on the terminal interval, expressed entirely
through the actual physical Hartree equation already defined in
`RegularRadiationFlow`. The time derivative is read in H^(L-2). -/
def IsRegularHartreeSolutionOn (κ : ℝ) (L : ℕ) (T τ : ℝ)
    (g : Sobolev L) (u : ℝ → Sobolev L) : Prop :=
  u T = g ∧
  ContinuousOn u (Icc (T - τ) T) ∧
  ∃ du : ℝ → SobolevR ((L : ℝ) - 2 * ((1 : ℕ) : ℝ)),
    ∀ t ∈ Icc (T - τ) T,
      HasDerivAt (fun s => sobolevDropTwo (u s)) (du t) t ∧
      HartreeEquationAt κ (u t) (du t).toDistr

/-- Approved external analytic boundary for the standard high-regularity
local theory. The parent structure records the actual equation, finite jets,
bounds and radiality. The additional fields make the two clauses omitted by
the earlier terminal explicit: uniqueness in the actual strong solution class
and C1 dependence into the normed terminal path space. -/
structure CitedHighRegularityHartreeLocalTheory (κ : ℝ)
    extends GeneralizedHartreeRegularLocalTheory κ where
  time_continuous : ∀ L, 4 ≤ L → ∀ T g,
    ‖g‖ ≤ epsilon L →
    ContinuousOn (flow L T g) (Icc (T - tau L) T)
  uniqueness : ∀ L, 4 ≤ L → ∀ T g,
    ‖g‖ ≤ epsilon L →
    ∀ u : ℝ → Sobolev L,
      IsRegularHartreeSolutionOn κ L T (tau L) g u →
      ∀ t ∈ Icc (T - tau L) T, u t = flow L T g t
  path : (L : ℕ) → ℝ → Sobolev L → RegularRadiationPath L
  path_apply : ∀ L T g σ,
    path L T g σ = flow L T g (terminalAffineTime T (tau L) σ)
  data_path_c1 : ∀ L, 4 ≤ L → ∀ T,
    ContDiffOn ℝ 1 (fun g : Sobolev L => path L T g)
      (Metric.ball 0 (epsilon L))

/-- The selected literature flow is genuinely a strong solution of the actual
inverse-square generalized Hartree equation on the terminal interval. -/
theorem cited_flow_is_regular_solution
    (κ : ℝ) (LT : CitedHighRegularityHartreeLocalTheory κ)
    {L : ℕ} (hL : 4 ≤ L) (T : ℝ) (g : Sobolev L)
    (hg : ‖g‖ ≤ LT.epsilon L) :
    IsRegularHartreeSolutionOn κ L T (LT.tau L) g (LT.flow L T g) := by
  refine ⟨LT.endpoint L T g, LT.time_continuous L hL T g hg, ?_⟩
  refine ⟨fun t => LT.jet L T g 1 t, ?_⟩
  intro t ht
  have hs := regularRadiation_strong_equation_certified κ
    LT.toGeneralizedHartreeRegularLocalTheory hL T g hg ht
  exact ⟨hs.1, hs.2.1⟩

/-- Exact specialization of manuscript `prop:regular-flow-stage3` relative to
the explicitly cited standard high-regularity local theory. In particular,
solution uniqueness and C1 dependence into a normed path space are no longer
omitted from the Lean terminal. -/
theorem regularRadiationFlow_originalEnvironment_closed
    (κ : ℝ) (LT : CitedHighRegularityHartreeLocalTheory κ)
    {N L : ℕ} (hN : 4 ≤ N) (hL : 2 * N + 8 ≤ L) :
    ∃ ε₀ τ₀ C : ℝ,
      0 < ε₀ ∧ 0 < τ₀ ∧ 0 < C ∧
      ∀ T : ℝ, ∃
        (z : Sobolev L → ℝ → Sobolev L)
        (zpath : Sobolev L → RegularRadiationPath L)
        (zjet : (g : Sobolev L) → (a : ℕ) → ℝ →
          SobolevR ((L : ℝ) - 2 * (a : ℝ))),
        (∀ g, z g T = g) ∧
        (∀ g σ, zpath g σ = z g (terminalAffineTime T τ₀ σ)) ∧
        ContDiffOn ℝ 1 zpath (Metric.ball 0 ε₀) ∧
        (∀ g, ‖g‖ ≤ ε₀ →
          IsRegularHartreeSolutionOn κ L T τ₀ g (z g)) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ u : ℝ → Sobolev L,
          IsRegularHartreeSolutionOn κ L T τ₀ g u →
          ∀ t ∈ Icc (T - τ₀) T, u t = z g t) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ t ∈ Icc (T - τ₀) T,
          ‖z g t‖ ≤ C * ‖g‖) ∧
        (∀ g, ‖g‖ ≤ ε₀ → IsRadialSobolev g →
          ∀ t ∈ Icc (T - τ₀) T, IsRadialSobolev (z g t)) ∧
        (∀ g t, (zjet g 0 t).toDistr = (z g t).toDistr) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ a : ℕ, a ≤ N + 2 →
          ∀ t ∈ Icc (T - τ₀) T, ‖zjet g a t‖ ≤ C * ‖g‖) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ a : ℕ, a ≤ N + 1 →
          ∀ t ∈ Icc (T - τ₀) T,
            HasDerivAt
              (fun s => sobolevWeaken (jetExponent_step L a) (zjet g a s))
              (zjet g (a + 1) t) t) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ t ∈ Icc (T - τ₀) T,
          HartreeEquationAt κ (z g t) (zjet g 1 t).toDistr ∧
          ∀ x : Space, Integrable (fun y : Space =>
            (kernel (x - y) : ℂ) * quarticDensity (physicalL2 (z g t)) y)) := by
  have hL4 : 4 ≤ L := by omega
  refine ⟨LT.epsilon L, LT.tau L, LT.boundConst L,
    LT.epsilon_pos L hL4, LT.tau_pos L hL4,
    LT.boundConst_pos L hL4, ?_⟩
  intro T
  refine ⟨LT.flow L T, LT.path L T, LT.jet L T,
    LT.endpoint L T, LT.path_apply L T, LT.data_path_c1 L hL4 T,
    ?_, ?_, LT.local_bound L hL4 T, LT.radial_preserved L hL4 T,
    LT.jet_zero L T, ?_, ?_, ?_⟩
  · intro g hg
    exact cited_flow_is_regular_solution κ LT hL4 T g hg
  · intro g hg u hu t ht
    exact LT.uniqueness L hL4 T g hg u hu t ht
  · intro g hg a ha t ht
    exact LT.jet_bound L hL4 T g hg a (by omega) t ht
  · intro g hg a ha t ht
    exact LT.jet_step L hL4 T g hg a (by omega) t ht
  · intro g hg t ht
    have hs := regularRadiation_strong_equation_certified κ
      LT.toGeneralizedHartreeRegularLocalTheory hL4 T g hg ht
    exact ⟨hs.2.1, hs.2.2⟩

#print axioms IsRegularHartreeSolutionOn
#print axioms CitedHighRegularityHartreeLocalTheory
#print axioms cited_flow_is_regular_solution
#print axioms regularRadiationFlow_originalEnvironment_closed

end HBL.RegularRadiation
