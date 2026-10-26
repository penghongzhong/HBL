import HBL.RegularRadiationKernel
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-!
# Standard high-regularity generalized Hartree local theory boundary

This is a universal, literature-level analysis interface, in the same sense as
`BCritical.CriticalLocalTheory` in the verified 3D NLS project.  It introduces
no Lean axiom and contains no blow-up-profile or modulation conclusion.

The intended source is Arora--Roudenko, J. Hyperbolic Differential Equations
17 (2020), 727--763, DOI 10.1142/S0219891620500228, together with the
standard persistence-of-regularity argument at integer Sobolev exponents.
The concrete inverse-square kernel and the order-zero seventh-order Hartree
estimate are verified natively in `RegularRadiationKernel.lean`.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology
namespace HBL.RegularRadiation

open BesselPotentialSpace TemperedDistribution

abbrev SobolevR (s : ℝ) :=
  BesselPotentialSpace Space ℂ s 2

abbrev Sobolev (L : ℕ) := SobolevR (L : ℝ)

/-- Canonical loss-of-regularity map between Bessel-potential Sobolev spaces.
It is built from Mathlib's proved monotonicity theorem, not assumed. -/
def sobolevWeaken {s s' : ℝ} (h : s' ≤ s) (f : SobolevR s) : SobolevR s' :=
  (BesselPotentialSpace.memSobolev_toDistr f).mono h |>.toBesselPotentialSpace

@[simp] theorem sobolevWeaken_toDistr {s s' : ℝ} (h : s' ≤ s) (f : SobolevR s) :
    (sobolevWeaken h f).toDistr = f.toDistr := by
  rfl

private theorem jetExponent_step (L a : ℕ) :
    (L : ℝ) - 2 * ((a + 1 : ℕ) : ℝ) ≤ (L : ℝ) - 2 * (a : ℝ) := by
  push_cast
  linarith

/-- Universal high-regularity local flow for the concrete generalized Hartree
equation with coefficient `κ`.  The fields are standard local-theory outputs:
terminal-value flow, persistence, local Lipschitz dependence, C¹ dependence on
terminal data, and the time-derivative hierarchy with two spatial derivatives
lost per time derivative.

This is an external theorem boundary, not a manuscript-specific result. -/
structure GeneralizedHartreeRegularLocalTheory (κ : ℝ) where
  epsilon : ℕ → ℝ
  tau : ℕ → ℝ
  boundConst : ℕ → ℝ
  flow : (L : ℕ) → ℝ → Sobolev L → ℝ → Sobolev L
  jet : (L : ℕ) → ℝ → Sobolev L → (a : ℕ) → ℝ →
    SobolevR ((L : ℝ) - 2 * (a : ℝ))
  epsilon_pos : ∀ L, 4 ≤ L → 0 < epsilon L
  tau_pos : ∀ L, 4 ≤ L → 0 < tau L
  boundConst_pos : ∀ L, 4 ≤ L → 0 < boundConst L
  endpoint : ∀ L T g, flow L T g T = g
  jet_zero : ∀ L T g t,
    (jet L T g 0 t).toDistr = (flow L T g t).toDistr
  jet_step : ∀ L T g a t,
    HasDerivAt
      (fun s => sobolevWeaken (jetExponent_step L a) (jet L T g a s))
      (jet L T g (a + 1) t) t
  local_bound : ∀ L, 4 ≤ L → ∀ T g,
    ‖g‖ ≤ epsilon L →
    ∀ t ∈ Icc (T - tau L) T,
      ‖flow L T g t‖ ≤ boundConst L * ‖g‖
  jet_bound : ∀ L, 4 ≤ L → ∀ T g,
    ‖g‖ ≤ epsilon L →
    ∀ a : ℕ, ∀ t ∈ Icc (T - tau L) T,
      ‖jet L T g a t‖ ≤ boundConst L * ‖g‖
  local_lipschitz : ∀ L, 4 ≤ L → ∀ T g h,
    ‖g‖ ≤ epsilon L → ‖h‖ ≤ epsilon L →
    ∀ t ∈ Icc (T - tau L) T,
      ‖flow L T g t - flow L T h t‖ ≤
        boundConst L * ‖g - h‖
  data_c1 : ∀ L, 4 ≤ L → ∀ T t,
    t ∈ Icc (T - tau L) T →
    ContDiff ℝ 1 (fun g : Sobolev L => flow L T g t)

/-- Exact terminal regular-radiation specialization used by the manuscript.
In particular, the full finite hierarchy
`0 ≤ a ≤ N+2` is retained, rather than replaced by an order-zero estimate. -/
theorem regularRadiationFlow_certified (κ : ℝ)
    (LT : GeneralizedHartreeRegularLocalTheory κ)
    {N L : ℕ} (hN : 4 ≤ N) (hL : 2 * N + 8 ≤ L) :
    ∃ ε₀ τ₀ C : ℝ,
      0 < ε₀ ∧ 0 < τ₀ ∧ 0 < C ∧
      ∀ T : ℝ, ∃
        z : Sobolev L → ℝ → Sobolev L,
        zjet : (g : Sobolev L) → (a : ℕ) → ℝ →
          SobolevR ((L : ℝ) - 2 * (a : ℝ)),
        (∀ g, z g T = g) ∧
        (∀ g t, (zjet g 0 t).toDistr = (z g t).toDistr) ∧
        (∀ g a t,
          HasDerivAt
            (fun s => sobolevWeaken (jetExponent_step L a) (zjet g a s))
            (zjet g (a + 1) t) t) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ t ∈ Icc (T - τ₀) T,
          ‖z g t‖ ≤ C * ‖g‖) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ a : ℕ, a ≤ N + 2 →
          ∀ t ∈ Icc (T - τ₀) T,
            ‖zjet g a t‖ ≤ C * ‖g‖) ∧
        (∀ g h, ‖g‖ ≤ ε₀ → ‖h‖ ≤ ε₀ →
          ∀ t ∈ Icc (T - τ₀) T,
            ‖z g t - z h t‖ ≤ C * ‖g - h‖) ∧
        (∀ t ∈ Icc (T - τ₀) T,
          ContDiff ℝ 1 (fun g : Sobolev L => z g t)) := by
  have hL4 : 4 ≤ L := by omega
  refine ⟨LT.epsilon L, LT.tau L, LT.boundConst L,
    LT.epsilon_pos L hL4, LT.tau_pos L hL4, LT.boundConst_pos L hL4, ?_⟩
  intro T
  let z : Sobolev L → ℝ → Sobolev L := fun g t => LT.flow L T g t
  let zj : Sobolev L → (a : ℕ) → ℝ →
      SobolevR ((L : ℝ) - 2 * (a : ℝ)) :=
    fun g a t => LT.jet L T g a t
  refine ⟨z, zj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    exact LT.endpoint L T g
  · intro g t
    exact LT.jet_zero L T g t
  · intro g a t
    exact LT.jet_step L T g a t
  · intro g hg t ht
    exact LT.local_bound L hL4 T g hg t ht
  · intro g hg a _ha t ht
    exact LT.jet_bound L hL4 T g hg a t ht
  · intro g h hg hh t ht
    exact LT.local_lipschitz L hL4 T g h hg hh t ht
  · intro t ht
    exact LT.data_c1 L hL4 T t ht

/-- The concrete equation-specific inverse-square kernel check remains native. -/
theorem regularRadiation_actualKernel_check :
    Integrable nearKernel ∧ 0 ≤ nearMass :=
  ⟨regularRadiationKernel_checks.1, regularRadiationKernel_checks.2.1⟩

#print axioms sobolevWeaken
#print axioms regularRadiationFlow_certified
#print axioms regularRadiation_actualKernel_check
end HBL.RegularRadiation
