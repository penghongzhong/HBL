import HBL.PhysicalEnergySurjectivity
import HBL.RadialHardy3D
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Real.Pi.Bounds

/-!
R14: an actual L6(R3) realization of the physical gradient completion.
The sixth-power bound is derived from the radial primitive and the existing
Hardy inequality, not imported as an additional assumption. Completion then
constructs the unique bounded linear extension of f -> (x -> f(norm x)).
The weak-gradient identification and the genuine 3D nonlocal Hessian remain
separate obligations. No injectivity of this L6 realization is asserted here.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem coreData (f : PhysicalGradientCore) :
    ContDiff ℝ 1 (f : ℝ → ℝ) ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R ≤ r → f r = 0 := by
  rcases f with ⟨f, hf⟩
  exact hf

private theorem coreMem (f : PhysicalGradientCore) :
    MemLp (deriv (radialU f)) 2 halfLineMeasure := by
  obtain ⟨hf, R, hR, hc⟩ := coreData f
  exact radialU_deriv_memLp_of_upperSupport f hf R hR hc

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

private theorem halfLine_integrable (F : ℝ → ℝ) (hF : Continuous F)
    (R : ℝ) (hR : 0 ≤ R) (hc : ∀ r : ℝ, R < r → F r = 0) :
    Integrable F halfLineMeasure := by
  have hi : IntegrableOn F (Ioc (0 : ℝ) R) :=
    hF.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have ht : IntegrableOn F (Ioi R) := by
    apply (integrable_zero ℝ ℝ (volume.restrict (Ioi R))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (hc r hr).symm
  change IntegrableOn F (Ioi (0 : ℝ))
  rw [← Ioc_union_Ioi_eq_Ioi hR]
  exact hi.union ht

private theorem coreNormIntegral (f : PhysicalGradientCore) :
    ‖f‖ ^ 2 = ∫ r, (deriv (radialU f) r) ^ 2 ∂halfLineMeasure := by
  change ‖smoothToRadialDotH1 f (coreMem f)‖ ^ 2 = _
  exact smoothRadialEnergy_coordinate_norm_sq f (coreMem f)

private theorem coreFiniteEnergy (f : PhysicalGradientCore) (r : ℝ) (hr : 0 ≤ r) :
    (∫ t in (0 : ℝ)..r, (deriv (radialU f) t) ^ 2) ≤ ‖f‖ ^ 2 := by
  rw [coreNormIntegral, intervalIntegral.integral_of_le hr]
  exact setIntegral_mono_set
    ((memLp_two_iff_integrable_sq (coreMem f).aestronglyMeasurable).mp (coreMem f))
    (Filter.Eventually.of_forall fun t => sq_nonneg _)
    (Filter.Eventually.of_forall fun _ ht => ht.1)

private theorem squareIntegralExpansion (q : ℝ → ℝ) (hq : Continuous q) (r a : ℝ) :
    (∫ t in (0 : ℝ)..r, (q t - a) ^ 2) =
      (∫ t in (0 : ℝ)..r, (q t) ^ 2) -
        (2 * a) * (∫ t in (0 : ℝ)..r, q t) + r * a ^ 2 := by
  have hqi : IntervalIntegrable q volume 0 r := hq.intervalIntegrable 0 r
  have hq2i : IntervalIntegrable (fun t => q t ^ 2) volume 0 r :=
    (hq.pow 2).intervalIntegrable 0 r
  have hlin : IntervalIntegrable (fun t => (2 * a) * q t) volume 0 r :=
    hqi.const_mul (2 * a)
  calc
    (∫ t in (0 : ℝ)..r, (q t - a) ^ 2) =
        ∫ t in (0 : ℝ)..r, ((q t) ^ 2 - (2 * a) * q t) + a ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = (∫ t in (0 : ℝ)..r, (q t) ^ 2 - (2 * a) * q t) +
        (∫ _t in (0 : ℝ)..r, a ^ 2) :=
      intervalIntegral.integral_add (hq2i.sub hlin) intervalIntegrable_const
    _ = _ := by
      rw [intervalIntegral.integral_sub hq2i hlin,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]

private theorem corePointwise (f : PhysicalGradientCore) (r : ℝ) (hr : 0 ≤ r) :
    r * (f r) ^ 2 ≤ ‖f‖ ^ 2 := by
  let q : ℝ → ℝ := deriv (radialU f)
  have hq : Continuous q := (radialU_contDiff_one f (coreData f).1).continuous_deriv_one
  have hpos : 0 ≤ ∫ t in (0 : ℝ)..r, (q t - f r) ^ 2 :=
    intervalIntegral.integral_nonneg hr (fun t _ => sq_nonneg _)
  have hpos' := hpos.trans_eq (squareIntegralExpansion q hq r (f r))
  have hprim : (∫ t in (0 : ℝ)..r, q t) = r * f r :=
    radialU_integral_deriv f (coreData f).1 r
  have hb := coreFiniteEnergy f r hr
  change (∫ t in (0 : ℝ)..r, (q t) ^ 2) ≤ ‖f‖ ^ 2 at hb
  rw [hprim] at hpos'
  nlinarith only [hpos', hb]

private theorem coreHardy (f : PhysicalGradientCore) :
    (∫ r, (f r) ^ 2 ∂halfLineMeasure) ≤ 4 * ‖f‖ ^ 2 := by
  obtain ⟨hf, R, hR, hc⟩ := coreData f
  rw [halfLine_cap (fun r => (f r) ^ 2) R hR (by
    intro r hr
    rw [hc r hr.le]
    norm_num)]
  have hh := radialHardy3D R hR f hf (hc R le_rfl)
  rw [← radialU_energy_identity R f hf (hc R le_rfl)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (coreFiniteEnergy f R hR) (by norm_num))

private theorem coreSixth (f : PhysicalGradientCore) :
    (∫ x : PhysicalRadialSpace3, (f ‖x‖) ^ 6) ≤ (16 * Real.pi) * ‖f‖ ^ 6 := by
  obtain ⟨hf, R, hR, hc⟩ := coreData f
  have hi2 : Integrable (fun r => (f r) ^ 2) halfLineMeasure :=
    halfLine_integrable _ (hf.continuous.pow 2) R hR (by
      intro r hr
      rw [hc r hr.le]
      norm_num)
  have hi6 : Integrable (fun r => r ^ 2 * (f r) ^ 6) halfLineMeasure :=
    halfLine_integrable _ ((continuous_id.pow 2).mul (hf.continuous.pow 6)) R hR (by
      intro r hr
      simp only [hc r hr.le, zero_pow (by norm_num : (6 : ℕ) ≠ 0), mul_zero])
  have hbound : (∫ r, r ^ 2 * (f r) ^ 6 ∂halfLineMeasure) ≤
      ‖f‖ ^ 4 * (∫ r, (f r) ^ 2 ∂halfLineMeasure) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hi6 (hi2.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hpoint := corePointwise f r hr.le
    have hp := pow_le_pow_left₀ (mul_nonneg hr.le (sq_nonneg (f r))) hpoint 2
    have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg (f r))
    nlinarith only [hm]
  have hrad : (∫ r, r ^ 2 * (f r) ^ 6 ∂halfLineMeasure) ≤ 4 * ‖f‖ ^ 6 := by
    have hh := mul_le_mul_of_nonneg_left (coreHardy f) (pow_nonneg (norm_nonneg f) 4)
    nlinarith only [hbound, hh]
  rw [physicalRadial3_integral (fun r => (f r) ^ 6)]
  have h := mul_le_mul_of_nonneg_left hrad (show (0 : ℝ) ≤ 4 * Real.pi by positivity)
  nlinarith only [h]

local instance : Fact ((1 : ENNReal) ≤ 6) := ⟨by norm_num⟩

/-- Actual three-dimensional real L6 space. -/
abbrev PhysicalL6 : Type := Lp ℝ 6 (volume : Measure PhysicalRadialSpace3)

private theorem coreLiftMem (f : PhysicalGradientCore) :
    MemLp (physicalRadial3_radialLift f) 6 (volume : Measure PhysicalRadialSpace3) := by
  obtain ⟨hf, R, hR, hc⟩ := coreData f
  have hs : HasCompactSupport (physicalRadial3_radialLift f) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : PhysicalRadialSpace3) R)
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hn
    exact hx (hc ‖x‖ (le_of_lt (lt_of_not_ge hn)))
  exact (hf.continuous.comp continuous_norm).memLp_of_hasCompactSupport hs

/-- Physical radial lift as an L6-valued linear map on the actual core. -/
def physicalCoreL6 : PhysicalGradientCore →ₗ[ℝ] PhysicalL6 where
  toFun f := (coreLiftMem f).toLp (physicalRadial3_radialLift f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(coreLiftMem (f + g)).coeFn_toLp,
      Lp.coeFn_add ((coreLiftMem f).toLp _) ((coreLiftMem g).toLp _),
      (coreLiftMem f).coeFn_toLp, (coreLiftMem g).coeFn_toLp] with x hs ha hf hg
    rw [hs, ha]
    simp only [Pi.add_apply, hf, hg]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(coreLiftMem (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((coreLiftMem f).toLp _),
      (coreLiftMem f).coeFn_toLp] with x hs hc hf
    simp only [RingHom.id_apply]
    rw [hs, hc]
    simp only [Pi.smul_apply, smul_eq_mul, hf]
    rfl

private theorem coreL6_norm (f : PhysicalGradientCore) :
    ‖physicalCoreL6 f‖ ≤ 2 * ‖f‖ := by
  have hpow : (∫ x : PhysicalRadialSpace3, ‖physicalRadial3_radialLift f x‖ ^ 6) ≤
      (2 * ‖f‖) ^ 6 := by
    have heq : (fun x : PhysicalRadialSpace3 => ‖physicalRadial3_radialLift f x‖ ^ 6) =
        (fun x => (f ‖x‖) ^ 6) := by
      funext x
      change |f ‖x‖| ^ 6 = (f ‖x‖) ^ 6
      exact (by decide : Even (6 : ℕ)).pow_abs (f ‖x‖)
    rw [heq]
    have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le
      (show (0 : ℝ) ≤ 16 * ‖f‖ ^ 6 by positivity)
    nlinarith only [coreSixth f, hpi]
  have hnonneg : 0 ≤ ∫ x : PhysicalRadialSpace3,
      ‖physicalRadial3_radialLift f x‖ ^ 6 := integral_nonneg (fun x => by positivity)
  have hroot := Real.rpow_le_rpow hnonneg hpow (show (0 : ℝ) ≤ (6 : ℝ)⁻¹ by norm_num)
  have hrhs : ((2 * ‖f‖) ^ 6) ^ (6 : ℝ)⁻¹ = 2 * ‖f‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hrhs] at hroot
  change ‖(coreLiftMem f).toLp (physicalRadial3_radialLift f)‖ ≤ _
  rw [Lp.norm_toLp,
    MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (6 : ENNReal) ≠ 0)
      (by norm_num : (6 : ENNReal) ≠ ⊤) (coreLiftMem f),
    ENNReal.toReal_ofReal (by positivity)]
  change (∫ x : PhysicalRadialSpace3,
    ‖physicalRadial3_radialLift f x‖ ^ (6 : ℝ)) ^ (6 : ℝ)⁻¹ ≤ 2 * ‖f‖
  have heq : (fun x : PhysicalRadialSpace3 =>
      ‖physicalRadial3_radialLift f x‖ ^ (6 : ℝ)) =
      (fun x => ‖physicalRadial3_radialLift f x‖ ^ (6 : ℕ)) := by
    funext x
    exact Real.rpow_natCast _ 6
  rw [heq]
  exact hroot

private def physicalCoreL6Continuous : PhysicalGradientCore →L[ℝ] PhysicalL6 :=
  physicalCoreL6.mkContinuous 2 coreL6_norm

/-- The constructed actual L6 representative of every completed energy state. -/
def physicalL6Realization : PhysicalRadialEnergyCompletion →L[ℝ] PhysicalL6 :=
  physicalCoreL6Continuous.fromCompletion

private theorem realization_on_core (f : PhysicalGradientCore) :
    physicalL6Realization (f : PhysicalRadialEnergyCompletion) = physicalCoreL6 f :=
  ContinuousLinearMap.fromCompletion_apply_coe physicalCoreL6Continuous f

private theorem realization_bound (u : PhysicalRadialEnergyCompletion) :
    ‖physicalL6Realization u‖ ≤ 2 * ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le physicalL6Realization.continuous.norm (continuous_const.mul continuous_norm)
  | ih f =>
    rw [realization_on_core, UniformSpace.Completion.norm_coe]
    exact coreL6_norm f

/-- Direct realization of every half-line energy coordinate in physical L6. -/
def physicalL6FromCoordinate : FullRadialEnergyL2 →L[ℝ] PhysicalL6 :=
  physicalL6Realization.comp physicalEnergyEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- R14: one complete environment. The Sobolev estimate, membership and
extension are conclusions. This does not claim a weak derivative or injectivity. -/
theorem physicalL6Realization_certified :
    (∀ f : PhysicalGradientCore,
      (∫ x : PhysicalRadialSpace3, (f ‖x‖) ^ 6) ≤ (16 * Real.pi) * ‖f‖ ^ 6) ∧
    (∀ f : PhysicalGradientCore,
      (physicalL6Realization (f : PhysicalRadialEnergyCompletion) : PhysicalRadialSpace3 → ℝ)
        =ᵐ[volume] physicalRadial3_radialLift f) ∧
    (∀ u : PhysicalRadialEnergyCompletion, ‖physicalL6Realization u‖ ≤ 2 * ‖u‖) ∧
    (∀ T : PhysicalRadialEnergyCompletion →L[ℝ] PhysicalL6,
      (∀ f : PhysicalGradientCore, T (f : PhysicalRadialEnergyCompletion) = physicalCoreL6 f) →
      T = physicalL6Realization) ∧
    (∀ q : FullRadialEnergyL2, ‖physicalL6FromCoordinate q‖ ≤ 2 * ‖q‖) ∧
    (∀ f : ℕ → PhysicalGradientCore, ∀ u : PhysicalRadialEnergyCompletion,
      Tendsto (fun n => (f n : PhysicalRadialEnergyCompletion)) atTop (𝓝 u) →
      Tendsto (fun n => physicalCoreL6 (f n)) atTop (𝓝 (physicalL6Realization u))) := by
  refine ⟨coreSixth, ?_, realization_bound, ?_, ?_, ?_⟩
  · intro f
    rw [realization_on_core]
    exact (coreLiftMem f).coeFn_toLp
  · intro T hT
    apply ContinuousLinearMap.ext
    intro u
    induction u using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq T.continuous physicalL6Realization.continuous
    | ih f => exact (hT f).trans (realization_on_core f).symm
  · intro q
    change ‖physicalL6Realization (physicalEnergyEquiv.symm q)‖ ≤ _
    simpa only [physicalEnergyEquiv.symm.norm_map] using
      realization_bound (physicalEnergyEquiv.symm q)
  · intro f u h
    have ht := physicalL6Realization.continuous.tendsto u |>.comp h
    simpa only [Function.comp_def, realization_on_core] using ht

end HBL.Modulation.Monopole
