import HBL.CompactTwoChannelCoercivity
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
R12: completion of the actual C1 radial gradient core.

The core consists of real C1 profiles vanishing beyond a finite positive
radius, not arbitrary vectors of a preassigned Hilbert space. Its induced
seminorm is proved to equal the actual three-dimensional Frechet gradient
seminorm divided by sqrt(4*pi). Completion separates its zero-energy
profiles (in particular irrelevant negative-radius extensions).

The coordinate extends isometrically into half-line L2. Onto-ness is NOT
assumed and is NOT needed to transfer the proved form coercivity. The
physical phase form and original radial nonlocal form extend continuously
and agree on the actual core. The complete 3D nonlocal angular identity,
identification with an L6/weak-derivative realization, and Hamilton
propagation remain separate obligations.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff RealInnerProductSpace Topology

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

private def gradientCoreSubmodule : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ 1 f ∧
    ∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R ≤ r → f r = 0}
  zero_mem' := by
    refine ⟨contDiff_const, 0, le_rfl, ?_⟩
    intro r _
    rfl
  add_mem' := by
    rintro f g ⟨hf, R, hR, hc⟩ ⟨hg, S, hS, hd⟩
    refine ⟨hf.add hg, max R S, hR.trans (le_max_left _ _), ?_⟩
    intro r hr
    change f r + g r = 0
    rw [hc r ((le_max_left _ _).trans hr), hd r ((le_max_right _ _).trans hr)]
    ring
  smul_mem' := by
    rintro c f ⟨hf, R, hR, hc⟩
    refine ⟨?_, R, hR, ?_⟩
    · exact contDiff_const.mul hf
    · intro r hr
      change c * f r = 0
      rw [hc r hr, mul_zero]

/-- Concrete compact radial profiles, before quotienting zero gradient. -/
def PhysicalGradientCore := ↥gradientCoreSubmodule

instance : AddCommGroup PhysicalGradientCore :=
  inferInstanceAs (AddCommGroup ↥gradientCoreSubmodule)
instance : Module ℝ PhysicalGradientCore :=
  inferInstanceAs (Module ℝ ↥gradientCoreSubmodule)
instance : CoeFun PhysicalGradientCore (fun _ => ℝ → ℝ) :=
  ⟨fun f => (show ↥gradientCoreSubmodule from f).val⟩

private theorem core_regular (f : PhysicalGradientCore) : ContDiff ℝ 1 f :=
  (show ↥gradientCoreSubmodule from f).property.1

private theorem core_support (f : PhysicalGradientCore) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R ≤ r → f r = 0 :=
  (show ↥gradientCoreSubmodule from f).property.2

private theorem core_memLp (f : PhysicalGradientCore) :
    MemLp (deriv (radialU f)) 2 halfLineMeasure := by
  obtain ⟨R, hR, hc⟩ := core_support f
  exact radialU_deriv_memLp_of_upperSupport f (core_regular f) R hR hc

/-- Actual derivative coordinate of the physical core; membership is derived. -/
def physicalCoreCoordinate : PhysicalGradientCore →ₗ[ℝ] FullRadialEnergyL2 where
  toFun f := smoothToRadialDotH1 f (core_memLp f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [smoothToRadialDotH1_ae (f + g) (core_memLp (f + g)),
      Lp.coeFn_add (smoothToRadialDotH1 f (core_memLp f))
        (smoothToRadialDotH1 g (core_memLp g)),
      smoothToRadialDotH1_ae f (core_memLp f),
      smoothToRadialDotH1_ae g (core_memLp g)] with r hsum ha hf hg
    rw [hsum, ha]
    simp only [Pi.add_apply, hf, hg]
    have heq : radialU (f + g) = radialU f + radialU g := by
      funext t
      change t * (f t + g t) = t * f t + t * g t
      ring
    rw [heq]
    exact deriv_add
      ((radialU_contDiff_one f (core_regular f)).differentiable (by norm_num) r)
      ((radialU_contDiff_one g (core_regular g)).differentiable (by norm_num) r)
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [smoothToRadialDotH1_ae (c • f) (core_memLp (c • f)),
      Lp.coeFn_smul c (smoothToRadialDotH1 f (core_memLp f)),
      smoothToRadialDotH1_ae f (core_memLp f)] with r hcf hc hf
    rw [hcf, hc]
    simp only [Pi.smul_apply, smul_eq_mul, hf, RingHom.id_apply]
    have heq : radialU (c • f) = fun t => c * radialU f t := by
      funext t
      change t * (c * f t) = c * (t * f t)
      ring
    rw [heq]
    exact (((radialU_contDiff_one f (core_regular f)).differentiable
      (by norm_num) r).hasDerivAt.const_mul c).deriv

/-- The seminorm will be identified with the actual physical gradient integral. -/
instance : SeminormedAddCommGroup PhysicalGradientCore :=
  SeminormedAddCommGroup.induced PhysicalGradientCore FullRadialEnergyL2
    physicalCoreCoordinate
instance : NormedSpace ℝ PhysicalGradientCore :=
  NormedSpace.induced ℝ PhysicalGradientCore FullRadialEnergyL2 physicalCoreCoordinate

private theorem core_norm (f : PhysicalGradientCore) :
    ‖physicalCoreCoordinate f‖ = ‖f‖ := rfl

private theorem core_physical_energy (f : PhysicalGradientCore) :
    (∫ x : PhysicalRadialSpace3,
      ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) =
      (4 * Real.pi) * ‖f‖ ^ 2 := by
  obtain ⟨R, hR, hc⟩ := core_support f
  simpa only [physicalCoreCoordinate, core_norm] using
    physicalRadial3_gradient_coordinate_of_upperSupport f (core_regular f) R hR hc

private def coreCoordinateContinuous : PhysicalGradientCore →L[ℝ] FullRadialEnergyL2 :=
  physicalCoreCoordinate.mkContinuous 1 (by intro f; change ‖physicalCoreCoordinate f‖ ≤
    1 * ‖physicalCoreCoordinate f‖; simp)

/-- Completion of the actual physical-gradient seminormed radial core. -/
abbrev PhysicalRadialEnergyCompletion := UniformSpace.Completion PhysicalGradientCore

/-- The unique continuous coordinate extension, constructed by completion. -/
def physicalEnergyEmbedding :
    PhysicalRadialEnergyCompletion →L[ℝ] FullRadialEnergyL2 :=
  coreCoordinateContinuous.fromCompletion

private theorem embedding_on_core (f : PhysicalGradientCore) :
    physicalEnergyEmbedding (f : PhysicalRadialEnergyCompletion) =
      physicalCoreCoordinate f :=
  ContinuousLinearMap.fromCompletion_apply_coe coreCoordinateContinuous f

private theorem embedding_norm (u : PhysicalRadialEnergyCompletion) :
    ‖physicalEnergyEmbedding u‖ = ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq physicalEnergyEmbedding.continuous.norm continuous_norm
  | ih f =>
    rw [embedding_on_core, UniformSpace.Completion.norm_coe]
    exact core_norm f

private theorem embedding_injective : Function.Injective physicalEnergyEmbedding := by
  intro u v huv
  have hnorm : ‖u - v‖ = 0 := by
    rw [← embedding_norm, map_sub, huv, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Continuous extension of the actual three-dimensional phase quadratic form. -/
def completedPhysicalPhaseForm (u : PhysicalRadialEnergyCompletion) : ℝ :=
  (4 * Real.pi) * inner ℝ (weightedVolterraAMinus (physicalEnergyEmbedding u))
    (physicalEnergyEmbedding u)

private theorem phase_continuous : Continuous completedPhysicalPhaseForm := by
  unfold completedPhysicalPhaseForm
  exact continuous_const.mul
    ((weightedVolterraAMinus.continuous.comp physicalEnergyEmbedding.continuous).inner
      physicalEnergyEmbedding.continuous)

private theorem phase_on_core (f : PhysicalGradientCore) :
    completedPhysicalPhaseForm (f : PhysicalRadialEnergyCompletion) =
      physicalRadial3PhaseQuadratic f := by
  obtain ⟨R, hR, hc⟩ := core_support f
  unfold completedPhysicalPhaseForm
  rw [embedding_on_core]
  exact (physicalRadial3_phase_core_eq_volterra f (core_regular f) R hR hc).symm

/-- Compact tests transported to the physical energy completion. -/
def completedPhaseTest : PhysicalRadialEnergyCompletion →L[ℝ] ℝ :=
  phaseCompactTest.comp physicalEnergyEmbedding

def completedScaleTest : PhysicalRadialEnergyCompletion →L[ℝ] ℝ :=
  scaleCompactTest.comp physicalEnergyEmbedding

/-- Extension of the original radial two-channel form. The 3D nonlocal
angular identity is not built into this definition. -/
def completedRadialTwoChannelForm (u v : PhysicalRadialEnergyCompletion) : ℝ :=
  (4 * Real.pi) *
    (inner ℝ (weightedVolterraAPlus (physicalEnergyEmbedding u)) (physicalEnergyEmbedding u) +
      inner ℝ (weightedVolterraAMinus (physicalEnergyEmbedding v)) (physicalEnergyEmbedding v))

private theorem two_channel_on_core (f g : PhysicalGradientCore) :
    completedRadialTwoChannelForm (f : PhysicalRadialEnergyCompletion)
      (g : PhysicalRadialEnergyCompletion) = (4 * Real.pi) * compactTwoChannelProfileForm f g := by
  unfold completedRadialTwoChannelForm
  rw [embedding_on_core, embedding_on_core]
  change (4 * Real.pi) *
    (inner ℝ (weightedVolterraAPlus (smoothToRadialDotH1 f (core_memLp f)))
        (smoothToRadialDotH1 f (core_memLp f)) +
      inner ℝ (weightedVolterraAMinus (smoothToRadialDotH1 g (core_memLp g)))
        (smoothToRadialDotH1 g (core_memLp g))) = _
  rw [weightedVolterraAPlus_radial_profile_pairing f f (core_regular f) (core_regular f)
      (core_memLp f) (core_memLp f),
    weightedVolterraAMinus_radial_profile_pairing g g (core_regular g) (core_regular g)
      (core_memLp g) (core_memLp g)]
  simp only [compactTwoChannelProfileForm, pow_two]

/-- R12: a complete physical-core completion environment. No density,
surjectivity, form equality, or existence of an extension is an input.
The ambient coordinate range need not be all of half-line L2 to transfer
coercivity to every element of this actual core completion. -/
theorem physicalEnergyCompletion_certified :
    (∀ f : PhysicalGradientCore,
      (∫ x : PhysicalRadialSpace3,
        ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) = (4 * Real.pi) * ‖f‖ ^ 2) ∧
    (∀ f : PhysicalGradientCore,
      physicalEnergyEmbedding (f : PhysicalRadialEnergyCompletion) = physicalCoreCoordinate f) ∧
    (∀ u : PhysicalRadialEnergyCompletion, ‖physicalEnergyEmbedding u‖ = ‖u‖) ∧
    Function.Injective physicalEnergyEmbedding ∧
    Continuous completedPhysicalPhaseForm ∧
    (∀ f : PhysicalGradientCore,
      completedPhysicalPhaseForm (f : PhysicalRadialEnergyCompletion) = physicalRadial3PhaseQuadratic f) ∧
    (∀ F : PhysicalRadialEnergyCompletion → ℝ, Continuous F →
      (∀ f : PhysicalGradientCore, F (f : PhysicalRadialEnergyCompletion) = physicalRadial3PhaseQuadratic f) →
      F = completedPhysicalPhaseForm) ∧
    (∀ f : PhysicalGradientCore,
      completedPhaseTest (f : PhysicalRadialEnergyCompletion) =
        ∫ r in (0 : ℝ)..Real.exp 1, normalizedZetaMinus r * radialU f r) ∧
    (∀ f : PhysicalGradientCore,
      completedScaleTest (f : PhysicalRadialEnergyCompletion) =
        ∫ r in (0 : ℝ)..Real.exp 1, normalizedZetaPlus r * radialU f r) ∧
    (∀ u : PhysicalRadialEnergyCompletion, completedPhaseTest u = 0 →
      phaseCompactGap * ((4 * Real.pi) * ‖u‖ ^ 2) ≤ completedPhysicalPhaseForm u) ∧
    (∀ f g : PhysicalGradientCore,
      completedRadialTwoChannelForm (f : PhysicalRadialEnergyCompletion)
        (g : PhysicalRadialEnergyCompletion) = (4 * Real.pi) * compactTwoChannelProfileForm f g) ∧
    (∀ u v : PhysicalRadialEnergyCompletion,
      completedScaleTest u = 0 → completedPhaseTest v = 0 →
      inner ℝ fullBubbleRadialEnergyL2 (physicalEnergyEmbedding u) = 0 →
      (4 * Real.pi) * compactTwoChannelGap * (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤
        completedRadialTwoChannelForm u v) := by
  refine ⟨core_physical_energy, embedding_on_core, embedding_norm, embedding_injective,
    phase_continuous, phase_on_core, ?_, ?_, ?_, ?_, two_channel_on_core, ?_⟩
  · intro F hF hcore
    funext u
    induction u using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq hF phase_continuous
    | ih f => exact (hcore f).trans (phase_on_core f).symm
  · intro f
    change phaseCompactTest (physicalEnergyEmbedding (f : PhysicalRadialEnergyCompletion)) = _
    rw [embedding_on_core]
    exact actualCompactPhaseSlice_certified.2.2.1 f (core_regular f) (core_memLp f)
  · intro f
    change scaleCompactTest (physicalEnergyEmbedding (f : PhysicalRadialEnergyCompletion)) = _
    rw [embedding_on_core]
    exact physicalScaleNormalization_certified.2.2.2.2.2.2.1 f (core_regular f) (core_memLp f)
  · intro u hu
    have h := actualCompactPhaseSlice_certified.2.2.2.1 (physicalEnergyEmbedding u) hu
    have hm := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 4 * Real.pi by positivity)
    rw [embedding_norm] at hm
    unfold completedPhysicalPhaseForm
    nlinarith only [hm]
  · intro u v hu hv hn
    have h := actualCompactTwoChannelCoercivity_certified.2.2.2.1
      (physicalEnergyEmbedding u) (physicalEnergyEmbedding v) hu hv hn
    have hm := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 4 * Real.pi by positivity)
    rw [embedding_norm, embedding_norm] at hm
    unfold completedRadialTwoChannelForm
    nlinarith only [hm]

end HBL.Modulation.Monopole
