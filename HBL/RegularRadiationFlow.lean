import HBL.RegularRadiationKernel
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-!
# Physical high-regularity Hartree local-theory boundary

The previous regularity-only interface did not state the PDE. Moreover,
BesselPotentialSpace.toLp represents J^L u, not u. This revision constructs
the physical L2 representative by first weakening to H^0, states the actual
inverse-square Hartree equation in tempered distributions, and restricts
jet estimates to the finite regularity budget and data regularity to a local
ball. It does not construct a value of the external local-theory structure.

Arora--Roudenko, J. Hyperbolic Differential Equations 17 (2020), 727--763,
DOI 10.1142/S0219891620500228 (arXiv:1910.01085, Theorem 1.1), supports
critical local well-posedness and local Lipschitz dependence. The additional
high-regularity persistence, finite time jets and local C1 dependence below
remain explicit external obligations, not consequences established merely
by citing that theorem. No blow-up or centre-propagator conclusion occurs.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology
namespace HBL.RegularRadiation

open BesselPotentialSpace TemperedDistribution

abbrev SobolevR (s : ℝ) := BesselPotentialSpace Space ℂ s 2
abbrev Sobolev (L : ℕ) := SobolevR (L : ℝ)

/-- The canonical loss-of-regularity map, constructed from Mathlib monotonicity. -/
def sobolevWeaken {s s' : ℝ} (h : s' ≤ s) (f : SobolevR s) : SobolevR s' :=
  (BesselPotentialSpace.memSobolev_toDistr f).mono h |>.toBesselPotentialSpace

@[simp] theorem sobolevWeaken_toDistr {s s' : ℝ} (h : s' ≤ s) (f : SobolevR s) :
    (sobolevWeaken h f).toDistr = f.toDistr := rfl

/-- The original physical function, not its Bessel-weighted transform. -/
def physicalL2 {L : ℕ} (f : Sobolev L) : Lp ℂ 2 (volume : Measure Space) :=
  (sobolevWeaken (show (0 : ℝ) ≤ (L : ℝ) from Nat.cast_nonneg L) f).toLp

/-- The physical representative defines exactly the original distribution. -/
theorem physicalL2_toDistr {L : ℕ} (f : Sobolev L) :
    (physicalL2 f : TemperedDistribution Space ℂ) = f.toDistr := by
  have h := (sobolevWeaken
    (show (0 : ℝ) ≤ (L : ℝ) from Nat.cast_nonneg L) f).bessel_toDistr_eq_toLp
  simpa only [physicalL2, TemperedDistribution.besselPotential_zero,
    ContinuousLinearMap.id_apply, sobolevWeaken_toDistr] using h.symm

/-- Native absolute-convergence estimate for the physical quartic potential.
Only the displayed L-infinity bound is needed beyond membership in H^L. -/
theorem physicalQuarticPotential_bound {L : ℕ} (f : Sobolev L)
    (R : ℝ) (hb : ∀ᵐ x, ‖physicalL2 f x‖ ≤ R) (x : Space) :
    Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) * quarticDensity (physicalL2 f) y) ∧
    ‖potential (quarticDensity (physicalL2 f)) x‖ ≤
      nearMass * R ^ 4 + R ^ 2 * (∫ y : Space, ‖physicalL2 f y‖ ^ 2) := by
  exact quartic_potential_bound (physicalL2 f) (Lp.memLp _) R hb x

/-- Radiality of the physical representative. -/
def IsRadialSobolev {L : ℕ} (f : Sobolev L) : Prop :=
  ∀ U : Space ≃ₗᵢ[ℝ] Space,
    (fun x => physicalL2 f (U x)) =ᵐ[volume] (fun x => physicalL2 f x)

private theorem jetExponent_step (L a : ℕ) :
    (L : ℝ) - 2 * ((a + 1 : ℕ) : ℝ) ≤ (L : ℝ) - 2 * (a : ℝ) := by
  push_cast
  linarith

/-- Read an H^L curve in the space of its first time derivative. -/
def sobolevDropTwo {L : ℕ} (f : Sobolev L) :
    SobolevR ((L : ℝ) - 2 * ((1 : ℕ) : ℝ)) :=
  sobolevWeaken (by simp only [Nat.cast_one, mul_one]; linarith) f

/-- The actual distributional Laplacian, with the correct two-derivative loss. -/
def sobolevLaplacian {s : ℝ} (f : SobolevR s) : SobolevR (s - 2) :=
  (BesselPotentialSpace.memSobolev_toDistr f).laplacian.toBesselPotentialSpace

@[simp] theorem sobolevLaplacian_toDistr {s : ℝ} (f : SobolevR s) :
    (sobolevLaplacian f).toDistr = Laplacian.laplacian f.toDistr := rfl

/-- The concrete focusing equation i*u_t + Delta*u + N_kappa(u) = 0.
The nonlinear witness must realize the actual kernel formula on the physical
representative. Absolute convergence is established separately below. -/
def HartreeEquationAt {L : ℕ} (κ : ℝ) (u : Sobolev L)
    (du : TemperedDistribution Space ℂ) : Prop :=
  ∃ n : Sobolev L,
    (fun x => physicalL2 n x) =ᵐ[volume]
      (fun x => hartreeNonlinearity κ (physicalL2 u) x) ∧
    Complex.I • du + Laplacian.laplacian u.toDistr + n.toDistr = 0

/-- Explicit external high-regularity solution-family input.
A proof of this structure's existence is not supplied by this file. -/
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
  jet_step : ∀ L, 4 ≤ L → ∀ T g,
    ‖g‖ ≤ epsilon L → ∀ a : ℕ, 2 * (a + 1) ≤ L →
    ∀ t ∈ Icc (T - tau L) T,
      HasDerivAt
        (fun s => sobolevWeaken (jetExponent_step L a) (jet L T g a s))
        (jet L T g (a + 1) t) t
  local_bound : ∀ L, 4 ≤ L → ∀ T g,
    ‖g‖ ≤ epsilon L → ∀ t ∈ Icc (T - tau L) T,
      ‖flow L T g t‖ ≤ boundConst L * ‖g‖
  physical_linfty : ∀ L, 4 ≤ L → ∀ T g,
    ‖g‖ ≤ epsilon L → ∀ t ∈ Icc (T - tau L) T,
      ∀ᵐ x, ‖physicalL2 (flow L T g t) x‖ ≤ boundConst L * ‖g‖
  jet_bound : ∀ L, 4 ≤ L → ∀ T g,
    ‖g‖ ≤ epsilon L → ∀ a : ℕ, 2 * a ≤ L →
    ∀ t ∈ Icc (T - tau L) T,
      ‖jet L T g a t‖ ≤ boundConst L * ‖g‖
  radial_preserved : ∀ L, 4 ≤ L → ∀ T g,
    ‖g‖ ≤ epsilon L → IsRadialSobolev g →
    ∀ t ∈ Icc (T - tau L) T, IsRadialSobolev (flow L T g t)
  local_lipschitz : ∀ L, 4 ≤ L → ∀ T g h,
    ‖g‖ ≤ epsilon L → ‖h‖ ≤ epsilon L →
    ∀ t ∈ Icc (T - tau L) T,
      ‖flow L T g t - flow L T h t‖ ≤ boundConst L * ‖g - h‖
  data_c1 : ∀ L, 4 ≤ L → ∀ T t,
    t ∈ Icc (T - tau L) T →
    ContDiffOn ℝ 1 (fun g : Sobolev L => flow L T g t)
      (Metric.ball 0 (epsilon L))
  equation : ∀ L, 4 ≤ L → ∀ T g,
    ‖g‖ ≤ epsilon L → ∀ t ∈ Icc (T - tau L) T,
      HartreeEquationAt κ (flow L T g t) (jet L T g 1 t).toDistr

/-- Native transfer from jets to the actual flow's strong time derivative,
together with the explicit PDE and absolute convergence of its convolution.
The external solution-family input remains visible. -/
theorem regularRadiation_strong_equation_certified (κ : ℝ)
    (LT : GeneralizedHartreeRegularLocalTheory κ)
    {L : ℕ} (hL : 4 ≤ L) (T : ℝ) (g : Sobolev L)
    (hg : ‖g‖ ≤ LT.epsilon L) {t : ℝ} (ht : t ∈ Icc (T - LT.tau L) T) :
    HasDerivAt (fun r => sobolevDropTwo (LT.flow L T g r))
      (LT.jet L T g 1 t) t ∧
    HartreeEquationAt κ (LT.flow L T g t) (LT.jet L T g 1 t).toDistr ∧
    ∀ x : Space, Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) * quarticDensity (physicalL2 (LT.flow L T g t)) y) := by
  have hd := LT.jet_step L hL T g hg 0 (by omega) t ht
  have he :
      (fun r => sobolevWeaken (jetExponent_step L 0) (LT.jet L T g 0 r)) =
      (fun r => sobolevDropTwo (LT.flow L T g r)) := by
    funext r
    apply BesselPotentialSpace.ext
    exact LT.jet_zero L T g r
  rw [he] at hd
  refine ⟨hd, LT.equation L hL T g hg t ht, ?_⟩
  intro x
  exact (physicalQuarticPotential_bound (LT.flow L T g t)
    (LT.boundConst L * ‖g‖) (LT.physical_linfty L hL T g hg t ht) x).1

/-- Corrected specialization of manuscript prop:regular-flow-stage3.
The original finite jet budget is retained and the concrete equation is now
part of the conclusion. This is conditional on the displayed local theory. -/
theorem regularRadiationFlow_certified (κ : ℝ)
    (LT : GeneralizedHartreeRegularLocalTheory κ)
    {N L : ℕ} (hN : 4 ≤ N) (hL : 2 * N + 8 ≤ L) :
    ∃ ε₀ τ₀ C : ℝ,
      0 < ε₀ ∧ 0 < τ₀ ∧ 0 < C ∧
      ∀ T : ℝ, ∃
        (z : Sobolev L → ℝ → Sobolev L)
        (zjet : (g : Sobolev L) → (a : ℕ) → ℝ →
          SobolevR ((L : ℝ) - 2 * (a : ℝ))),
        (∀ g, z g T = g) ∧
        (∀ g t, (zjet g 0 t).toDistr = (z g t).toDistr) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ a : ℕ, 2 * (a + 1) ≤ L →
          ∀ t ∈ Icc (T - τ₀) T,
            HasDerivAt
              (fun s => sobolevWeaken (jetExponent_step L a) (zjet g a s))
              (zjet g (a + 1) t) t) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ t ∈ Icc (T - τ₀) T,
          ‖z g t‖ ≤ C * ‖g‖) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ a : ℕ, a ≤ N + 2 →
          ∀ t ∈ Icc (T - τ₀) T, ‖zjet g a t‖ ≤ C * ‖g‖) ∧
        (∀ g, ‖g‖ ≤ ε₀ → IsRadialSobolev g →
          ∀ t ∈ Icc (T - τ₀) T, IsRadialSobolev (z g t)) ∧
        (∀ g h, ‖g‖ ≤ ε₀ → ‖h‖ ≤ ε₀ →
          ∀ t ∈ Icc (T - τ₀) T, ‖z g t - z h t‖ ≤ C * ‖g - h‖) ∧
        (∀ t ∈ Icc (T - τ₀) T,
          ContDiffOn ℝ 1 (fun g : Sobolev L => z g t) (Metric.ball 0 ε₀)) ∧
        (∀ g, ‖g‖ ≤ ε₀ → ∀ t ∈ Icc (T - τ₀) T,
          HasDerivAt (fun r => sobolevDropTwo (z g r)) (zjet g 1 t) t ∧
          HartreeEquationAt κ (z g t) (zjet g 1 t).toDistr ∧
          ∀ x : Space, Integrable (fun y : Space =>
            (kernel (x - y) : ℂ) * quarticDensity (physicalL2 (z g t)) y)) := by
  have hL4 : 4 ≤ L := le_trans hN (by omega)
  refine ⟨LT.epsilon L, LT.tau L, LT.boundConst L,
    LT.epsilon_pos L hL4, LT.tau_pos L hL4, LT.boundConst_pos L hL4, ?_⟩
  intro T
  refine ⟨LT.flow L T, LT.jet L T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact LT.endpoint L T
  · exact LT.jet_zero L T
  · exact LT.jet_step L hL4 T
  · exact LT.local_bound L hL4 T
  · intro g hg a ha t ht
    exact LT.jet_bound L hL4 T g hg a (by omega) t ht
  · exact LT.radial_preserved L hL4 T
  · exact LT.local_lipschitz L hL4 T
  · exact LT.data_c1 L hL4 T
  · intro g hg t ht
    exact regularRadiation_strong_equation_certified κ LT hL4 T g hg ht

/-- The concrete inverse-square kernel check remains native. -/
theorem regularRadiation_actualKernel_check :
    Integrable nearKernel ∧ 0 ≤ nearMass :=
  ⟨regularRadiationKernel_checks.1, regularRadiationKernel_checks.2.1⟩

end HBL.RegularRadiation
