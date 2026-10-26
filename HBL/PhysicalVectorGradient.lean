import HBL.PhysicalWeakRadial
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher

/-!
R16: the full three-dimensional L2 weak gradient of the SAME L6 realization.
The core map is the actual Mathlib gradient (the Riesz representative of the
Frechet derivative), not a new radial formula. Its squared L2 norm is the
physical integral already established in R12. Lipschitz integration by parts
handles the possible nondifferentiability at the origin without a new boundary
condition. Both weak pairings are continuous, so completion identifies the
Cartesian weak derivative of the existing L6 representative. No Hamilton
flow, nonlocal angular identity, or converse Sobolev density is asserted.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace NNReal

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

local instance : Fact ((1 : ENNReal) ≤ 6) := ⟨by norm_num⟩
local instance : ENNReal.HolderConjugate (6 / 5) 6 where
  inv_add_inv_eq_inv := by
    rw [ENNReal.inv_div (Or.inl (by norm_num : (5 : ENNReal) ≠ ⊤))
        (Or.inl (by norm_num : (5 : ENNReal) ≠ 0)),
      ENNReal.div_eq_inv_mul, ← mul_add_one,
      show (5 + 1 : ENNReal) = 6 by norm_num,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), inv_one]
local instance : Fact ((1 : ENNReal) ≤ 6 / 5) :=
  ⟨ENNReal.HolderConjugate.one_le (6 / 5) 6⟩

/-- Genuine vector fields in physical three-dimensional Lebesgue L2. -/
abbrev PhysicalVectorL2 := Lp PhysicalRadialSpace3 2 (volume : Measure PhysicalRadialSpace3)

private theorem coreData (f : PhysicalGradientCore) :
    ContDiff ℝ 1 (f : ℝ → ℝ) ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R ≤ r → f r = 0 := by
  rcases f with ⟨f, hf⟩
  exact hf

private theorem coreDiff (f : PhysicalGradientCore) (x : PhysicalRadialSpace3) (hx : x ≠ 0) :
    DifferentiableAt ℝ (physicalRadial3_radialLift f) x :=
  ((coreData f).1.differentiable (by norm_num) ‖x‖).comp x
    ((contDiffAt_norm ℝ (n := 1) hx).differentiableAt (by norm_num))

private theorem gradientNorm (f : PhysicalGradientCore) (x : PhysicalRadialSpace3) :
    ‖gradient (physicalRadial3_radialLift f) x‖ =
      ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ :=
  (InnerProductSpace.toDual ℝ PhysicalRadialSpace3).symm.norm_map _

private theorem gradientMem (f : PhysicalGradientCore) :
    MemLp (gradient (physicalRadial3_radialLift f)) 2
      (volume : Measure PhysicalRadialSpace3) := by
  have hm : Measurable (gradient (physicalRadial3_radialLift f)) :=
    (InnerProductSpace.toDual ℝ PhysicalRadialSpace3).symm.continuous.measurable.comp
      (measurable_fderiv ℝ (physicalRadial3_radialLift f))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  simpa only [gradientNorm] using (physicalEnergyCompletion_certified.1 f).1

/-- The actual Euclidean gradient on the original radial core. -/
def physicalCoreGradient : PhysicalGradientCore →ₗ[ℝ] PhysicalVectorL2 where
  toFun f := (gradientMem f).toLp (gradient (physicalRadial3_radialLift f))
  map_add' f g := by
    apply Lp.ext
    have hn : ∀ᵐ x : PhysicalRadialSpace3 ∂volume, x ≠ 0 := by simp [ae_iff]
    filter_upwards [(gradientMem (f + g)).coeFn_toLp,
      Lp.coeFn_add ((gradientMem f).toLp _) ((gradientMem g).toLp _),
      (gradientMem f).coeFn_toLp, (gradientMem g).coeFn_toLp, hn] with x hs ha hf hg hx
    rw [hs, ha]
    simp only [Pi.add_apply, hf, hg]
    have he : physicalRadial3_radialLift (f + g : PhysicalGradientCore) =
        physicalRadial3_radialLift f + physicalRadial3_radialLift g := rfl
    simp only [gradient, he, fderiv_add (coreDiff f x hx) (coreDiff g x hx), map_add]
  map_smul' c f := by
    apply Lp.ext
    have hn : ∀ᵐ x : PhysicalRadialSpace3 ∂volume, x ≠ 0 := by simp [ae_iff]
    filter_upwards [(gradientMem (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((gradientMem f).toLp _), (gradientMem f).coeFn_toLp, hn]
      with x hs hc hf hx
    simp only [RingHom.id_apply]
    rw [hs, hc]
    simp only [Pi.smul_apply, hf]
    have he : physicalRadial3_radialLift (c • f : PhysicalGradientCore) =
        c • physicalRadial3_radialLift f := rfl
    simp only [gradient, he, fderiv_const_smul (coreDiff f x hx) c, map_smul]

private theorem coreGradient_ae (f : PhysicalGradientCore) :
    (physicalCoreGradient f : PhysicalRadialSpace3 → PhysicalRadialSpace3) =ᵐ[volume]
      gradient (physicalRadial3_radialLift f) := (gradientMem f).coeFn_toLp

private theorem coreGradientEnergy (f : PhysicalGradientCore) :
    ‖physicalCoreGradient f‖ ^ 2 = (4 * Real.pi) * ‖f‖ ^ 2 := by
  calc
    ‖physicalCoreGradient f‖ ^ 2 =
        inner ℝ (physicalCoreGradient f) (physicalCoreGradient f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x : PhysicalRadialSpace3, ‖gradient (physicalRadial3_radialLift f) x‖ ^ 2 := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [coreGradient_ae f] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    _ = (4 * Real.pi) * ‖f‖ ^ 2 := by
      simp_rw [gradientNorm]
      exact physicalEnergyCompletion_certified.2.1 f

private theorem coreGradientBound (f : PhysicalGradientCore) :
    ‖physicalCoreGradient f‖ ≤ Real.sqrt (4 * Real.pi) * ‖f‖ := by
  have he := coreGradientEnergy f
  have hs : (Real.sqrt (4 * Real.pi)) ^ 2 = 4 * Real.pi := Real.sq_sqrt (by positivity)
  have hp := norm_nonneg (physicalCoreGradient f)
  have hq : 0 ≤ Real.sqrt (4 * Real.pi) * ‖f‖ := by positivity
  nlinarith

private def coreGradientContinuous : PhysicalGradientCore →L[ℝ] PhysicalVectorL2 :=
  physicalCoreGradient.mkContinuous (Real.sqrt (4 * Real.pi)) coreGradientBound

/-- Constructed physical vector gradient of the completed energy state. -/
def physicalGradientRealization : PhysicalRadialEnergyCompletion →L[ℝ] PhysicalVectorL2 :=
  coreGradientContinuous.fromCompletion

private theorem gradient_on_core (f : PhysicalGradientCore) :
    physicalGradientRealization (f : PhysicalRadialEnergyCompletion) = physicalCoreGradient f :=
  ContinuousLinearMap.fromCompletion_apply_coe coreGradientContinuous f

private theorem gradient_energy (u : PhysicalRadialEnergyCompletion) :
    ‖physicalGradientRealization u‖ ^ 2 = (4 * Real.pi) * ‖u‖ ^ 2 := by
  induction u using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (physicalGradientRealization.continuous.norm.pow 2)
      (continuous_const.mul (continuous_norm.pow 2))
  | ih f =>
    rw [gradient_on_core, UniformSpace.Completion.norm_coe]
    exact coreGradientEnergy f

private theorem core_lipschitz (f : PhysicalGradientCore) :
    ∃ C : ℝ≥0, LipschitzWith C (physicalRadial3_radialLift f) := by
  obtain ⟨hf, R, hR, hc⟩ := coreData f
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuous_deriv_one.continuousOn : ContinuousOn (deriv (f : ℝ → ℝ)) (Icc 0 R))
  let C : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hb : ∀ r ∈ Ici (0 : ℝ), ‖deriv (f : ℝ → ℝ) r‖₊ ≤ C := by
    intro r hr
    change ‖deriv (f : ℝ → ℝ) r‖ ≤ max M 0
    by_cases hle : r ≤ R
    · exact (hM r ⟨hr, hle⟩).trans (le_max_left _ _)
    · have he : (f : ℝ → ℝ) =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds (lt_of_not_ge hle)] with t ht
        exact hc t ht.le
      rw [he.deriv_eq, deriv_const]
      simpa only [norm_zero] using (le_max_right M 0)
  have hl : LipschitzOnWith C (f : ℝ → ℝ) (Ici 0) :=
    Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun r _ => hf.differentiable (by norm_num) r) hb (convex_Ici (0 : ℝ))
  refine ⟨C, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  exact (hl.dist_le_mul ‖x‖ (norm_nonneg x) ‖y‖ (norm_nonneg y)).trans
    (mul_le_mul_of_nonneg_left (dist_norm_norm_le x y) C.coe_nonneg)

private theorem derivativeTestMem (φ : PhysicalRadialSpace3 → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v : PhysicalRadialSpace3) :
    MemLp (fun x => fderiv ℝ φ x v) (6 / 5) (volume : Measure PhysicalRadialSpace3) := by
  have hd : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact hd.memLp_of_hasCompactSupport (hc.fderiv_apply ℝ v)

private theorem vectorTestMem (φ : PhysicalRadialSpace3 → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v : PhysicalRadialSpace3) :
    MemLp (fun x => φ x • v) 2 (volume : Measure PhysicalRadialSpace3) := by
  have hs : HasCompactSupport (fun x => φ x • v) := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro x hx
    by_contra hn
    apply hx
    change φ x • v = 0
    rw [image_eq_zero_of_notMem_tsupport hn, zero_smul]
  exact (hφ.continuous.smul continuous_const).memLp_of_hasCompactSupport hs

private def derivativeTestPair (φ : PhysicalRadialSpace3 → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v : PhysicalRadialSpace3) :
    PhysicalL6 →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume : Measure PhysicalRadialSpace3)
    (6 / 5) 6 ((derivativeTestMem φ hφ hc v).toLp (fun x => fderiv ℝ φ x v))

private def vectorTestPair (φ : PhysicalRadialSpace3 → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v : PhysicalRadialSpace3) :
    PhysicalVectorL2 →L[ℝ] ℝ :=
  innerSL ℝ ((vectorTestMem φ hφ hc v).toLp (fun x => φ x • v))

private theorem derivative_pair (φ : PhysicalRadialSpace3 → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v : PhysicalRadialSpace3) (f : PhysicalL6) :
    derivativeTestPair φ hφ hc v f = ∫ x, fderiv ℝ φ x v * f x := by
  unfold derivativeTestPair
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(derivativeTestMem φ hφ hc v).coeFn_toLp] with x hx
  change _ * f x = _
  rw [hx]

private theorem vector_pair (φ : PhysicalRadialSpace3 → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v : PhysicalRadialSpace3) (G : PhysicalVectorL2) :
    vectorTestPair φ hφ hc v G = ∫ x, φ x * inner ℝ v (G x) := by
  change inner ℝ ((vectorTestMem φ hφ hc v).toLp _) G = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(vectorTestMem φ hφ hc v).coeFn_toLp] with x hx
  rw [hx, real_inner_smul_left]

private theorem core_ibp (f : PhysicalGradientCore) (φ : PhysicalRadialSpace3 → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v : PhysicalRadialSpace3) :
    (∫ x, φ x * inner ℝ v (gradient (physicalRadial3_radialLift f) x)) =
      -(∫ x, fderiv ℝ φ x v * physicalRadial3_radialLift f x) := by
  obtain ⟨C, hC⟩ := core_lipschitz f
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ (by norm_num)
  calc
    (∫ x, φ x * inner ℝ v (gradient (physicalRadial3_radialLift f) x)) =
        ∫ x, lineDeriv ℝ (physicalRadial3_radialLift f) x v * φ x := by
      apply integral_congr_ae
      have hn : ∀ᵐ x : PhysicalRadialSpace3 ∂volume, x ≠ 0 := by simp [ae_iff]
      filter_upwards [hn] with x hx
      rw [(coreDiff f x hx).lineDeriv_eq_fderiv]
      simp only [inner_gradient_right, conj_trivial, mul_comm]
    _ = ∫ x, lineDeriv ℝ φ x (-v) * physicalRadial3_radialLift f x :=
      hC.integral_lineDeriv_mul_eq hD hc v
    _ = -(∫ x, fderiv ℝ φ x v * physicalRadial3_radialLift f x) := by
      simp_rw [(hφ.differentiable (by norm_num) _).lineDeriv_eq_fderiv, map_neg, neg_mul]
      exact integral_neg _

private theorem completed_ibp (u : PhysicalRadialEnergyCompletion)
    (φ : PhysicalRadialSpace3 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (v : PhysicalRadialSpace3) :
    vectorTestPair φ hφ hc v (physicalGradientRealization u) =
      -derivativeTestPair φ hφ hc v (physicalL6Realization u) := by
  induction u using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((vectorTestPair φ hφ hc v).continuous.comp physicalGradientRealization.continuous)
      (((derivativeTestPair φ hφ hc v).continuous.comp physicalL6Realization.continuous).neg)
  | ih f =>
    rw [gradient_on_core, vector_pair, derivative_pair]
    calc
      (∫ x, φ x * inner ℝ v (physicalCoreGradient f x)) =
          ∫ x, φ x * inner ℝ v (gradient (physicalRadial3_radialLift f) x) := by
        apply integral_congr_ae
        filter_upwards [coreGradient_ae f] with x hx
        rw [hx]
      _ = -(∫ x, fderiv ℝ φ x v * physicalRadial3_radialLift f x) := core_ibp f φ hφ hc v
      _ = -(∫ x, fderiv ℝ φ x v * physicalL6Realization (f : PhysicalRadialEnergyCompletion) x) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [physicalL6Realization_certified.2.1 f] with x hx
        rw [hx]

/-- Full Cartesian distributional weak-gradient identity, with absolute
integrability included; tests and directions are arbitrary in three dimensions. -/
def IsPhysicalVectorWeakGradient (f : PhysicalL6) (G : PhysicalVectorL2) : Prop :=
  ∀ φ : PhysicalRadialSpace3 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∀ v : PhysicalRadialSpace3,
      Integrable (fun x => fderiv ℝ φ x v * f x) ∧
      Integrable (fun x => φ x * inner ℝ v (G x)) ∧
      (∫ x, φ x * inner ℝ v (G x)) = -(∫ x, fderiv ℝ φ x v * f x)

private theorem gradient_weak (u : PhysicalRadialEnergyCompletion) :
    IsPhysicalVectorWeakGradient (physicalL6Realization u) (physicalGradientRealization u) := by
  intro φ hφ hc v
  refine ⟨?_, ?_, ?_⟩
  · exact memLp_one_iff_integrable.mp
      ((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1
        (derivativeTestMem φ hφ hc v) (Lp.memLp (physicalL6Realization u)))
  · have hi := memLp_one_iff_integrable.mp
      ((innerSL ℝ : PhysicalRadialSpace3 →L[ℝ] PhysicalRadialSpace3 →L[ℝ] ℝ).memLp_of_bilin 1
        (vectorTestMem φ hφ hc v) (Lp.memLp (physicalGradientRealization u)))
    change Integrable (fun x => inner ℝ (φ x • v) (physicalGradientRealization u x)) at hi
    simpa only [real_inner_smul_left] using hi
  · rw [← vector_pair φ hφ hc v, ← derivative_pair φ hφ hc v]
    exact completed_ibp u φ hφ hc v

/-- One complete R16 environment: the actual full vector weak gradient of
R14's L6 function, exact physical energy and strong core approximation.
No gradient existence, integration-by-parts identity or norm equality is assumed. -/
theorem physicalVectorGradient_certified :
    (∀ f : PhysicalGradientCore,
      (physicalGradientRealization (f : PhysicalRadialEnergyCompletion) :
        PhysicalRadialSpace3 → PhysicalRadialSpace3) =ᵐ[volume]
          gradient (physicalRadial3_radialLift f)) ∧
    (∀ u : PhysicalRadialEnergyCompletion,
      IsPhysicalVectorWeakGradient (physicalL6Realization u) (physicalGradientRealization u)) ∧
    (∀ u : PhysicalRadialEnergyCompletion,
      ‖physicalGradientRealization u‖ ^ 2 = (4 * Real.pi) * ‖u‖ ^ 2) ∧
    (∀ q : FullRadialEnergyL2,
      ‖physicalGradientRealization (physicalEnergyEquiv.symm q)‖ ^ 2 =
        (4 * Real.pi) * ‖q‖ ^ 2) ∧
    (∀ T : PhysicalRadialEnergyCompletion →L[ℝ] PhysicalVectorL2,
      (∀ f : PhysicalGradientCore, T (f : PhysicalRadialEnergyCompletion) = physicalCoreGradient f) →
      T = physicalGradientRealization) ∧
    (∀ f : ℕ → PhysicalGradientCore, ∀ u : PhysicalRadialEnergyCompletion,
      Tendsto (fun n => (f n : PhysicalRadialEnergyCompletion)) atTop (𝓝 u) →
      Tendsto (fun n => physicalCoreGradient (f n)) atTop (𝓝 (physicalGradientRealization u))) := by
  refine ⟨?_, gradient_weak, gradient_energy, ?_, ?_, ?_⟩
  · intro f
    rw [gradient_on_core]
    exact coreGradient_ae f
  · intro q
    rw [gradient_energy, physicalEnergyEquiv.symm.norm_map]
  · intro T hT
    apply ContinuousLinearMap.ext
    intro u
    induction u using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq T.continuous physicalGradientRealization.continuous
    | ih f => exact (hT f).trans (gradient_on_core f).symm
  · intro f u h
    have ht := physicalGradientRealization.continuous.tendsto u |>.comp h
    simpa only [Function.comp_def, gradient_on_core] using ht

end HBL.Modulation.Monopole
