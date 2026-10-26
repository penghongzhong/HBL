import HBL.CompactTwoChannelCoercivity
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
R12: completion of the actual C1 radial gradient core.
The actual physical integrals are proved integrable. The core seminorm
is exactly its three-dimensional Frechet gradient seminorm divided by
sqrt(4*pi). Completion separates zero energy. The coordinate extends
isometrically into half-line L2, without assuming surjectivity. The
physical phase form extends uniquely and the original radial two-channel
form and compact constraints extend with their coercivity. Identification
with an L6/weak-derivative realization, the genuine 3D nonlocal angular
identity, and Hamilton propagation are not asserted.
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
abbrev PhysicalGradientCore := ↥gradientCoreSubmodule

private theorem core_regular (f : PhysicalGradientCore) : ContDiff ℝ 1 (f : ℝ → ℝ) :=
  f.property.1

private theorem core_support (f : PhysicalGradientCore) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R ≤ r → f r = 0 :=
  f.property.2

private theorem core_memLp (f : PhysicalGradientCore) :
    MemLp (deriv (radialU f)) 2 halfLineMeasure := by
  obtain ⟨R, hR, hc⟩ := core_support f
  exact radialU_deriv_memLp_of_upperSupport f (core_regular f) R hR hc

private theorem radial_integrable_of_upper_support
    (F : ℝ → ℝ) (hF : Continuous F) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ r : ℝ, R < r → F r = 0) :
    Integrable (fun x : PhysicalRadialSpace3 => F ‖x‖) := by
  have hleft : IntegrableOn (fun r : ℝ => r ^ 2 * F r) (Ioc (0 : ℝ) R) :=
    ((continuous_id.pow 2).mul hF).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have htail : IntegrableOn (fun r : ℝ => r ^ 2 * F r) (Ioi R) := by
    apply (integrable_zero ℝ ℝ (volume.restrict (Ioi R))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change (0 : ℝ) = r ^ 2 * F r
    rw [hc r hr, mul_zero]
  have hrad : IntegrableOn (fun r : ℝ => r ^ 2 * F r) (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hR]
    exact hleft.union htail
  have hdim : Module.finrank ℝ PhysicalRadialSpace3 = 3 := by
    simp [PhysicalRadialSpace3]
  apply (integrable_fun_norm_addHaar (volume : Measure PhysicalRadialSpace3)).2
  simpa only [hdim, Nat.reduceSub, smul_eq_mul] using hrad

private theorem core_gradient_integrable (f : PhysicalGradientCore) :
    Integrable (fun x : PhysicalRadialSpace3 =>
      ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) := by
  obtain ⟨R, hR, hc⟩ := core_support f
  have hd : ∀ r : ℝ, R < r → deriv (f : ℝ → ℝ) r = 0 := by
    intro r hr
    have he : (f : ℝ → ℝ) =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hr] with t ht
      exact hc t (le_of_lt ht)
    exact ((hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq he).deriv
  have hi := radial_integrable_of_upper_support
    (fun r => (deriv (f : ℝ → ℝ) r) ^ 2)
    ((core_regular f).continuous_deriv_one.pow 2) R hR (by
      intro r hr
      rw [hd r hr]
      norm_num)
  apply hi.congr
  have hne : ∀ᵐ x : PhysicalRadialSpace3 ∂volume, x ≠ 0 := by simp [ae_iff]
  filter_upwards [hne] with x hx
  exact (physicalRadial3_radial_fderiv_norm_sq f (core_regular f) x hx).symm

private theorem core_potential_integrable (f : PhysicalGradientCore) :
    Integrable (fun x : PhysicalRadialSpace3 =>
      bubble ‖x‖ ^ 4 * f ‖x‖ * f ‖x‖) := by
  obtain ⟨R, hR, hc⟩ := core_support f
  apply radial_integrable_of_upper_support
    (fun r => bubble r ^ 4 * f r * f r)
    (((bubble_contDiff.continuous.pow 4).mul (core_regular f).continuous).mul
      (core_regular f).continuous) R hR
  intro r hr
  rw [hc r hr.le, mul_zero, mul_zero]

/-- Actual derivative coordinate of the physical core; membership is derived. -/
def physicalCoreCoordinate : PhysicalGradientCore →ₗ[ℝ] FullRadialEnergyL2 where
  toFun f := smoothToRadialDotH1 f (core_memLp f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [smoothToRadialDotH1_ae (f + g : PhysicalGradientCore) (core_memLp (f + g)),
      Lp.coeFn_add (smoothToRadialDotH1 f (core_memLp f))
        (smoothToRadialDotH1 g (core_memLp g)),
      smoothToRadialDotH1_ae f (core_memLp f),
      smoothToRadialDotH1_ae g (core_memLp g)] with r hsum ha hf hg
    rw [hsum, ha]
    simp only [Pi.add_apply, hf, hg]
    have heq : radialU (f + g : PhysicalGradientCore) = radialU f + radialU g := by
      funext t
      change t * (f t + g t) = t * f t + t * g t
      ring
    rw [heq]
    exact deriv_add
      ((radialU_contDiff_one f (core_regular f)).differentiable (by norm_num) r)
      ((radialU_contDiff_one g (core_regular g)).differentiable (by norm_num) r)
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [smoothToRadialDotH1_ae (c • f : PhysicalGradientCore) (core_memLp (c • f)),
      Lp.coeFn_smul c (smoothToRadialDotH1 f (core_memLp f)),
      smoothToRadialDotH1_ae f (core_memLp f)] with r hcf hc hf
    rw [hcf, hc]
    simp only [Pi.smul_apply, smul_eq_mul, hf, RingHom.id_apply]
    have heq : radialU (c • f : PhysicalGradientCore) = fun t => c * radialU f t := by
      funext t
      change t * (c * f t) = c * (t * f t)
      ring
    rw [heq]
    exact (((radialU_contDiff_one f (core_regular f)).differentiable
      (by norm_num) r).hasDerivAt.const_mul c).deriv

/-- The seminorm is identified below with the integrable physical gradient. -/
instance : SeminormedAddCommGroup PhysicalGradientCore :=
  SeminormedAddCommGroup.induced PhysicalGradientCore FullRadialEnergyL2 physicalCoreCoordinate
instance : NormedSpace ℝ PhysicalGradientCore :=
  NormedSpace.induced ℝ PhysicalGradientCore FullRadialEnergyL2 physicalCoreCoordinate

private theorem core_norm (f : PhysicalGradientCore) :
    ‖physicalCoreCoordinate f‖ = ‖f‖ := rfl

private theorem core_physical_energy (f : PhysicalGradientCore) :
    (∫ x : PhysicalRadialSpace3,
      ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) =
      (4 * Real.pi) * ‖f‖ ^ 2 := by
  obtain ⟨R, hR, hc⟩ := core_support f
  change (∫ x : PhysicalRadialSpace3,
      ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) =
    (4 * Real.pi) * ‖smoothToRadialDotH1 f (core_memLp f)‖ ^ 2
  exact physicalRadial3_gradient_coordinate_of_upperSupport f (core_regular f) R hR hc

private def coreCoordinateContinuous : PhysicalGradientCore →L[ℝ] FullRadialEnergyL2 :=
  physicalCoreCoordinate.mkContinuous 1 (by
    intro f
    change ‖physicalCoreCoordinate f‖ ≤ 1 * ‖physicalCoreCoordinate f‖
    simp)

/-- Completion of the actual physical-gradient seminormed radial core. -/
abbrev PhysicalRadialEnergyCompletion := UniformSpace.Completion PhysicalGradientCore

/-- The continuous coordinate extension, constructed by completion. -/
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

/-- Extension of the actual three-dimensional phase quadratic form. -/
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

/-- Original compact tests transported to the physical energy completion. -/
def completedPhaseTest : PhysicalRadialEnergyCompletion →L[ℝ] ℝ :=
  phaseCompactTest.comp physicalEnergyEmbedding

def completedScaleTest : PhysicalRadialEnergyCompletion →L[ℝ] ℝ :=
  scaleCompactTest.comp physicalEnergyEmbedding

/-- Extension of the original radial two-channel form, not a postulated
three-dimensional nonlocal angular identity. -/
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

/-- R12: one complete physical-core completion environment. No existence
of an extension, isometry, form identity, or coercivity is a hypothesis.
Onto-ness of the coordinate map and a physical Hamilton flow are not claimed. -/
theorem physicalEnergyCompletion_certified :
    (∀ f : PhysicalGradientCore,
      Integrable (fun x : PhysicalRadialSpace3 =>
        ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) ∧
      Integrable (fun x : PhysicalRadialSpace3 => bubble ‖x‖ ^ 4 * f ‖x‖ * f ‖x‖)) ∧
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
  refine ⟨(fun f => ⟨core_gradient_integrable f, core_potential_integrable f⟩),
    core_physical_energy, embedding_on_core, embedding_norm, embedding_injective,
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
