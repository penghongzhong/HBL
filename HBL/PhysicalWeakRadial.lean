import HBL.PhysicalL6Realization
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
R15: identify the weak radial coordinate of the SAME physical L6 realization.
Using tests r^2 * phi avoids division by the radius at the origin. The physical
weight is 2*phi(|x|)+|x|*phi'(|x|). Both pairings are constructed continuous
linear functionals. The identity is proved by actual core integration by
parts and extended by completion. Smooth test separation proves uniqueness
of the energy coordinate and injectivity of the L6 realization.
This is radial distributional identification, not yet the full Cartesian
weak-gradient construction or the three-dimensional nonlocal Hessian.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

local instance : Fact ((1 : ENNReal) ≤ 6) := ⟨by norm_num⟩
local instance : Fact ((1 : ENNReal) ≤ 6 / 5) := ⟨by norm_num⟩
local instance : ENNReal.HolderConjugate (6 / 5) 6 := ⟨by norm_num⟩

/-- Nonsingular physical weight corresponding to the radial test r^2 phi. -/
def physicalWeakRadialWeight (φ : ℝ → ℝ) (x : PhysicalRadialSpace3) : ℝ :=
  2 * φ ‖x‖ + ‖x‖ * deriv φ ‖x‖

private theorem test_coordinate_mem (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    MemLp (fun r : ℝ => r ^ 2 * φ r) 2 halfLineMeasure := by
  have hs : HasCompactSupport (fun r : ℝ => r ^ 2 * φ r) := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro r hr
    by_contra hn
    exact hr (by rw [image_eq_zero_of_notMem_tsupport hn, mul_zero])
  exact ((continuous_id.pow 2).mul hφ.continuous).memLp_of_hasCompactSupport hs

private theorem physical_weight_mem (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    MemLp (physicalWeakRadialWeight φ) (6 / 5)
      (volume : Measure PhysicalRadialSpace3) := by
  have hd : Continuous (deriv φ) :=
    ((contDiff_infty_iff_deriv.mp hφ).2).continuous
  have hcont : Continuous (physicalWeakRadialWeight φ) :=
    ((continuous_const.mul hφ.continuous).add (continuous_id.mul hd)).comp continuous_norm
  obtain ⟨M, hM⟩ := hc.isCompact.bddAbove
  have hs : HasCompactSupport (physicalWeakRadialWeight φ) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : PhysicalRadialSpace3) (max 0 M))
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hn
    have hout : ‖x‖ ∉ tsupport φ := by
      intro h
      exact hn ((hM h).trans (le_max_right _ _))
    exact hx (by
      unfold physicalWeakRadialWeight
      rw [image_eq_zero_of_notMem_tsupport hout, deriv_of_notMem_tsupport hout]
      ring)
  exact hcont.memLp_of_hasCompactSupport hs

private def physicalTestPair (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : PhysicalL6 →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume : Measure PhysicalRadialSpace3)
    (6 / 5) 6 ((physical_weight_mem φ hφ hc).toLp (physicalWeakRadialWeight φ))

private theorem physical_pair_eq (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v : PhysicalL6) :
    physicalTestPair φ hφ hc v =
      ∫ x : PhysicalRadialSpace3, physicalWeakRadialWeight φ x * v x := by
  unfold physicalTestPair
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(physical_weight_mem φ hφ hc).coeFn_toLp] with x hx
  change _ * v x = _
  rw [hx]

private theorem physical_pair_integrable (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v : PhysicalL6) :
    Integrable (fun x : PhysicalRadialSpace3 => physicalWeakRadialWeight φ x * v x) :=
  memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1
      (physical_weight_mem φ hφ hc) (Lp.memLp v))

private def radialTestPair (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : FullRadialEnergyL2 →L[ℝ] ℝ :=
  innerSL ℝ ((test_coordinate_mem φ hφ hc).toLp (fun r => r ^ 2 * φ r))

private theorem radial_pair_eq (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (q : FullRadialEnergyL2) :
    radialTestPair φ hφ hc q =
      ∫ r, (r ^ 2 * φ r) * q r ∂halfLineMeasure := by
  change inner ℝ ((test_coordinate_mem φ hφ hc).toLp _) q = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(test_coordinate_mem φ hφ hc).coeFn_toLp] with r hr
  simp only [hr, Real.inner_apply]

private theorem radial_pair_integrable (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (q : FullRadialEnergyL2) :
    Integrable (fun r => (r ^ 2 * φ r) * q r) halfLineMeasure := by
  exact memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1
      (test_coordinate_mem φ hφ hc) (Lp.memLp q))

private theorem halfLine_cap (F : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ r : ℝ, R < r → F r = 0) :
    (∫ r, F r ∂halfLineMeasure) = ∫ r in (0 : ℝ)..R, F r := by
  change (∫ r in Ioi (0 : ℝ), F r) = _
  rw [intervalIntegral.integral_of_le hR]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc (0 : ℝ) R ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
  intro r hr
  apply hc
  by_contra hn
  exact hr.2 ⟨hr.1, le_of_not_gt hn⟩

private theorem core_data (f : PhysicalGradientCore) :
    ContDiff ℝ 1 (f : ℝ → ℝ) ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R ≤ r → f r = 0 := by
  rcases f with ⟨f, hf⟩
  exact hf

private theorem core_ibp (f : PhysicalGradientCore) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ r, r ^ 2 * ((2 * φ r + r * deriv φ r) * f r) ∂halfLineMeasure) =
      -(∫ r, (r ^ 2 * φ r) * deriv (radialU f) r ∂halfLineMeasure) := by
  have hf := (core_data f).1
  obtain ⟨M, hM⟩ := hc.isCompact.bddAbove
  let R : ℝ := max 0 (M + 1)
  have hR : 0 ≤ R := le_max_left _ _
  have hout (r : ℝ) (hr : R ≤ r) : r ∉ tsupport φ := by
    intro h
    have hm := hM h
    have hbound : M + 1 ≤ R := le_max_right _ _
    linarith
  have hz (r : ℝ) (hr : R ≤ r) : φ r = 0 :=
    image_eq_zero_of_notMem_tsupport (hout r hr)
  have hdz (r : ℝ) (hr : R ≤ r) : deriv φ r = 0 :=
    deriv_of_notMem_tsupport (hout r hr)
  rw [halfLine_cap _ R hR (by intro r hr; simp only [hz r hr.le, hdz r hr.le, mul_zero, add_zero]),
    halfLine_cap _ R hR (by intro r hr; simp only [hz r hr.le, mul_zero, zero_mul])]
  have hd (r : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2 * φ t)
      (2 * r * φ r + r ^ 2 * deriv φ r) r := by
    have h := ((hasDerivAt_id r).pow 2).mul
      ((hφ.differentiable (by norm_num) r).hasDerivAt)
    apply h.congr_deriv
    ring
  have hdc : Continuous (fun r : ℝ => 2 * r * φ r + r ^ 2 * deriv φ r) :=
    ((continuous_const.mul continuous_id).mul hφ.continuous).add
      ((continuous_id.pow 2).mul ((contDiff_infty_iff_deriv.mp hφ).2).continuous)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := R) (u := radialU f)
    (u' := deriv (radialU f)) (v := fun r : ℝ => r ^ 2 * φ r)
    (v' := fun r : ℝ => 2 * r * φ r + r ^ 2 * deriv φ r)
    (fun r _ => ((radialU_contDiff_one f hf).differentiable (by norm_num) r).hasDerivAt)
    (fun r _ => hd r)
    ((radialU_contDiff_one f hf).continuous_deriv_one.intervalIntegrable 0 R)
    (hdc.intervalIntegrable 0 R)
  have hparts' : (∫ r in (0 : ℝ)..R,
      radialU f r * (2 * r * φ r + r ^ 2 * deriv φ r)) =
      -(∫ r in (0 : ℝ)..R, deriv (radialU f) r * (r ^ 2 * φ r)) := by
    simpa only [hz R le_rfl, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_mul, sub_zero, zero_sub] using hparts
  calc
    (∫ r in (0 : ℝ)..R, r ^ 2 * ((2 * φ r + r * deriv φ r) * f r)) =
        ∫ r in (0 : ℝ)..R, radialU f r * (2 * r * φ r + r ^ 2 * deriv φ r) := by
      apply intervalIntegral.integral_congr
      intro r _
      dsimp [radialU]
      ring
    _ = _ := by
      rw [hparts']
      congr 1
      apply intervalIntegral.integral_congr
      intro r _
      ring

private theorem core_pair (f : PhysicalGradientCore) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    physicalTestPair φ hφ hc (physicalL6Realization (f : PhysicalRadialEnergyCompletion)) =
      -(4 * Real.pi) * radialTestPair φ hφ hc (physicalCoreCoordinate f) := by
  rw [physical_pair_eq, radial_pair_eq]
  have hfae := physicalL6Realization_certified.2.1 f
  obtain ⟨hf, R, hR, hcut⟩ := core_data f
  have hqae : (physicalCoreCoordinate f : ℝ → ℝ) =ᵐ[halfLineMeasure]
      deriv (radialU f) :=
    smoothToRadialDotH1_ae f (radialU_deriv_memLp_of_upperSupport f hf R hR hcut)
  have hp : (∫ x : PhysicalRadialSpace3,
      physicalWeakRadialWeight φ x * physicalL6Realization (f : PhysicalRadialEnergyCompletion) x) =
      ∫ x : PhysicalRadialSpace3, (2 * φ ‖x‖ + ‖x‖ * deriv φ ‖x‖) * f ‖x‖ := by
    apply integral_congr_ae
    filter_upwards [hfae] with x hx
    rw [hx]
    rfl
  have hq : (∫ r, (r ^ 2 * φ r) * physicalCoreCoordinate f r ∂halfLineMeasure) =
      ∫ r, (r ^ 2 * φ r) * deriv (radialU f) r ∂halfLineMeasure := by
    apply integral_congr_ae
    filter_upwards [hqae] with r hr
    rw [hr]
  rw [hp, hq, physicalRadial3_integral (fun r => (2 * φ r + r * deriv φ r) * f r)]
  change (4 * Real.pi) * (∫ r, r ^ 2 * ((2 * φ r + r * deriv φ r) * f r)
    ∂halfLineMeasure) = _
  rw [core_ibp f φ hφ hc]
  ring

private theorem completed_pair (u : PhysicalRadialEnergyCompletion) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    physicalTestPair φ hφ hc (physicalL6Realization u) =
      -(4 * Real.pi) * radialTestPair φ hφ hc (physicalEnergyEmbedding u) := by
  induction u using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((physicalTestPair φ hφ hc).continuous.comp physicalL6Realization.continuous)
      (continuous_const.mul ((radialTestPair φ hφ hc).continuous.comp
        physicalEnergyEmbedding.continuous))
  | ih f =>
    rw [physicalEnergyCompletion_certified.2.2.1 f]
    exact core_pair f φ hφ hc

private theorem tests_separate_zero (q : FullRadialEnergyL2)
    (hq : ∀ φ : ℝ → ℝ, ∀ hφ : ContDiff ℝ ∞ φ, ∀ hc : HasCompactSupport φ,
      radialTestPair φ hφ hc q = 0) : q = 0 := by
  have hl : LocallyIntegrable (q : ℝ → ℝ) halfLineMeasure :=
    (Lp.memLp q).locallyIntegrable (by norm_num)
  have hlw : LocallyIntegrable (fun r : ℝ => q r * r ^ 2) halfLineMeasure := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    exact (hl.integrableOn_isCompact hK).mul_continuousOn
      (continuous_id.pow 2).continuousOn hK
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero hlw (fun φ hφ hc => by
    have h := hq φ hφ hc
    rw [radial_pair_eq] at h
    convert h using 1
    apply integral_congr_ae
    filter_upwards with r
    simp only [smul_eq_mul]
    ring)
  apply Lp.ext
  filter_upwards [hz, ae_restrict_mem measurableSet_Ioi,
    Lp.coeFn_zero ℝ 2 halfLineMeasure] with r hr hrpos hzero
  have hqr : q r = 0 := (mul_eq_zero.mp hr).resolve_right (pow_ne_zero 2 hrpos.ne')
  simpa only [Pi.zero_apply] using hqr.trans hzero.symm

private theorem tests_separate (q p : FullRadialEnergyL2)
    (h : ∀ φ : ℝ → ℝ, ∀ hφ : ContDiff ℝ ∞ φ, ∀ hc : HasCompactSupport φ,
      radialTestPair φ hφ hc q = radialTestPair φ hφ hc p) : q = p := by
  apply sub_eq_zero.mp
  apply tests_separate_zero
  intro φ hφ hc
  rw [map_sub, h φ hφ hc, sub_self]

/-- Weak identification in terms of actual integrals of the physical L6 function.
Tests r^2 phi determine the entire half-line L2 coordinate, not just a quotient. -/
def IsPhysicalWeakRadialCoordinate (v : PhysicalL6) (q : FullRadialEnergyL2) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x : PhysicalRadialSpace3, physicalWeakRadialWeight φ x * v x) =
      -(4 * Real.pi) * (∫ r, (r ^ 2 * φ r) * q r ∂halfLineMeasure)

private theorem weak_coordinate (u : PhysicalRadialEnergyCompletion) :
    IsPhysicalWeakRadialCoordinate (physicalL6Realization u) (physicalEnergyEmbedding u) := by
  intro φ hφ hc
  rw [← physical_pair_eq φ hφ hc, ← radial_pair_eq φ hφ hc]
  exact completed_pair u φ hφ hc

private theorem weak_unique (v : PhysicalL6) (q p : FullRadialEnergyL2)
    (hq : IsPhysicalWeakRadialCoordinate v q) (hp : IsPhysicalWeakRadialCoordinate v p) : q = p := by
  apply tests_separate
  intro φ hφ hc
  have he := (hq φ hφ hc).symm.trans (hp φ hφ hc)
  rw [← radial_pair_eq φ hφ hc, ← radial_pair_eq φ hφ hc] at he
  exact mul_left_cancel₀ (by positivity : -(4 * Real.pi) ≠ 0) he

private theorem realization_injective : Function.Injective physicalL6Realization := by
  intro u v huv
  apply physicalEnergyCompletion_certified.2.2.2.2.1
  apply weak_unique (physicalL6Realization u)
  · exact weak_coordinate u
  · rw [huv]
    exact weak_coordinate v

/-- One complete R15 environment. No weak-coordinate identity, separation,
injectivity, or physical test continuity is an input hypothesis. -/
theorem physicalWeakRadial_certified :
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ u : PhysicalRadialEnergyCompletion,
      Integrable (fun x : PhysicalRadialSpace3 =>
        physicalWeakRadialWeight φ x * physicalL6Realization u x) ∧
      Integrable (fun r => (r ^ 2 * φ r) * physicalEnergyEmbedding u r) halfLineMeasure) ∧
    (∀ u : PhysicalRadialEnergyCompletion,
      IsPhysicalWeakRadialCoordinate (physicalL6Realization u) (physicalEnergyEmbedding u)) ∧
    (∀ v : PhysicalL6, ∀ q p : FullRadialEnergyL2,
      IsPhysicalWeakRadialCoordinate v q → IsPhysicalWeakRadialCoordinate v p → q = p) ∧
    (∀ u : PhysicalRadialEnergyCompletion, ∃! q : FullRadialEnergyL2,
      IsPhysicalWeakRadialCoordinate (physicalL6Realization u) q) ∧
    Function.Injective physicalL6Realization ∧
    Function.Injective physicalL6FromCoordinate := by
  refine ⟨?_, weak_coordinate, weak_unique, ?_, realization_injective, ?_⟩
  · intro φ hφ hc u
    exact ⟨physical_pair_integrable φ hφ hc (physicalL6Realization u),
      radial_pair_integrable φ hφ hc (physicalEnergyEmbedding u)⟩
  · intro u
    exact ⟨physicalEnergyEmbedding u, weak_coordinate u,
      fun q hq => weak_unique (physicalL6Realization u) q (physicalEnergyEmbedding u)
        hq (weak_coordinate u)⟩
  · intro q p hqp
    apply physicalEnergyEquiv.symm.injective
    apply realization_injective
    exact hqp

end HBL.Modulation.Monopole
