import HBL.PhysicalEnergyCompletion
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
R13: surjectivity of the actual physical-gradient completion coordinate.
The orthogonal-complement proof constructs a compact C1 radial primitive
for every smooth zero-integral test supported away from zero. Thus an
L2 vector annihilating the actual core is constant as a distribution on
the positive half-line. Its L2 membership forces that constant to vanish.
The closed range of the already proved isometry is therefore all L2.
No density, surjectivity, inverse, or physical Sobolev realization is
assumed. The L6/weak-gradient realization and the 3D nonlocal angular
identity remain separate obligations.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem upper_support_bound (g : ℝ → ℝ) (hg : HasCompactSupport g) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R ≤ r → g r = 0 := by
  obtain ⟨b, hb⟩ := hg.bddAbove
  refine ⟨max 0 (b + 1), le_max_left _ _, ?_⟩
  intro r hr
  apply Function.notMem_support.mp
  intro hmem
  have hb' := hb (subset_tsupport g hmem)
  have hr' := (le_max_right 0 (b + 1)).trans hr
  linarith

private theorem lower_support_bound (g : ℝ → ℝ)
    (hg : tsupport g ⊆ Ioi (0 : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℝ, r ≤ a → g r = 0 := by
  have hz : (0 : ℝ) ∉ tsupport g := by
    intro h
    exact lt_irrefl 0 (hg h)
  have he : g =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) :=
    (notMem_tsupport_iff_eventuallyEq).mp hz
  obtain ⟨e, hepos, he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨e / 2, half_pos hepos, ?_⟩
  intro r hr
  by_cases hnonpos : r ≤ 0
  · apply Function.notMem_support.mp
    intro hm
    exact (not_lt_of_ge hnonpos) (hg (subset_tsupport g hm))
  · apply he
    rw [Real.dist_eq, sub_zero, abs_of_pos (lt_of_not_ge hnonpos)]
    linarith

private def unitTest (r : ℝ) : ℝ :=
  normalizedZetaMinus r * radialResonanceMinus r

private theorem unitTest_smooth : ContDiff ℝ ∞ unitTest :=
  normalizedZetaMinus_contDiff_infty.mul radialResonanceMinus_contDiff_infty

private theorem unitTest_compact : HasCompactSupport unitTest :=
  normalizedZetaMinus_hasCompactSupport.mul_right

private theorem unitTest_lower (r : ℝ) (hr : r ≤ (1 / 4 : ℝ)) :
    unitTest r = 0 := by
  have hb : thresholdBump r = 0 := by
    apply thresholdBump.zero_of_le_dist
    change (1 / 4 : ℝ) ≤ dist r (1 / 2 : ℝ)
    rw [Real.dist_eq, abs_of_nonpos (by linarith : r - (1 / 2 : ℝ) ≤ 0)]
    linarith
  simp [unitTest, normalizedZetaMinus, hb]

private theorem unitTest_upper (r : ℝ) (hr : 1 ≤ r) : unitTest r = 0 := by
  simp [unitTest, normalizedZetaMinus_zero_of_one_le r hr]

private theorem unitTest_integral : (∫ r : ℝ, unitTest r) = 1 := by
  have hsupport : (∫ r in Ioc (0 : ℝ) (Real.exp 1), unitTest r) =
      ∫ r : ℝ, unitTest r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    by_cases hpos : 0 < r
    · have hge : Real.exp 1 < r := by
        by_contra h
        exact hr ⟨hpos, le_of_not_gt h⟩
      exact unitTest_upper r (le_trans (Real.one_le_exp (by norm_num)) hge.le)
    · exact unitTest_lower r (le_trans (le_of_not_gt hpos) (by norm_num))
  have hn := normalizedZetaMinus_normalized
  rw [intervalIntegral.integral_of_le (Real.exp_pos 1).le] at hn
  exact hsupport.symm.trans hn

private theorem zero_mean_core
    (h : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R)
    (hlower : ∀ r : ℝ, r ≤ a → h r = 0)
    (hupper : ∀ r : ℝ, R ≤ r → h r = 0)
    (hmean : (∫ r : ℝ, h r) = 0) :
    ∃ f : PhysicalGradientCore, deriv (radialU f) = h := by
  let P : ℝ → ℝ := fun r => ∫ t in (0 : ℝ)..r, h t
  have hP (r : ℝ) : HasDerivAt P (h r) r :=
    intervalIntegral.integral_hasDerivAt_right
      (hh.continuous.intervalIntegrable 0 r)
      hh.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hh.continuous.continuousAt
  have hPC : ContDiff ℝ 1 P := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun r => (hP r).differentiableAt, ?_⟩
    have he : deriv P = h := funext (fun r => (hP r).deriv)
    rw [he]
    exact hh.continuous
  have hPnear (r : ℝ) (hr : r < a) : P r = 0 := by
    calc
      P r = ∫ t in (0 : ℝ)..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hlower t (le_trans ht.2 (max_le ha.le hr.le))
      _ = 0 := by simp
  have hPfar (r : ℝ) (hr : R ≤ r) : P r = 0 := by
    change (∫ t in (0 : ℝ)..r, h t) = 0
    rw [intervalIntegral.integral_of_le (hR.trans hr)]
    calc
      (∫ t in Ioc (0 : ℝ) r, h t) = ∫ t : ℝ, h t := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro t ht
        by_cases hp : 0 < t
        · have hrt : r < t := by
            by_contra hn
            exact ht ⟨hp, le_of_not_gt hn⟩
          exact hupper t (hr.trans hrt.le)
        · exact hlower t ((le_of_not_gt hp).trans ha.le)
      _ = 0 := hmean
  let f : ℝ → ℝ := fun r => P r / r
  have hf : ContDiff ℝ 1 f := by
    apply contDiff_iff_contDiffAt.mpr
    intro r
    by_cases hr : r = 0
    · subst r
      have he : f =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => 0) := by
        filter_upwards [Iio_mem_nhds ha] with t ht
        dsimp [f]
        rw [hPnear t ht, zero_div]
      exact contDiffAt_const.congr_of_eventuallyEq he
    · exact hPC.contDiffAt.div contDiffAt_id hr
  have hfc : ∀ r : ℝ, R ≤ r → f r = 0 := by
    intro r hr
    dsimp [f]
    rw [hPfar r hr, zero_div]
  let fc : PhysicalGradientCore := ⟨f, hf, R, hR, hfc⟩
  refine ⟨fc, ?_⟩
  have hU : radialU fc = P := by
    funext r
    change r * (P r / r) = P r
    by_cases hr : r = 0
    · subst r
      simp [P]
    · field_simp
  rw [hU]
  exact funext (fun r => (hP r).deriv)

private theorem coordinate_pairing (f : PhysicalGradientCore)
    (q : FullRadialEnergyL2) :
    inner ℝ (physicalCoreCoordinate f) q =
      ∫ r : ℝ, deriv (radialU f) r * q r ∂halfLineMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have he : (physicalCoreCoordinate f : ℝ → ℝ) =ᵐ[halfLineMeasure]
      deriv (radialU f) := smoothToRadialDotH1_ae f _
  filter_upwards [he] with r hr
  rw [hr, Real.inner_apply]

private theorem annihilator_zero (q : FullRadialEnergyL2)
    (hq : ∀ f : PhysicalGradientCore, inner ℝ (physicalCoreCoordinate f) q = 0) :
    q = 0 := by
  let c : ℝ := ∫ r : ℝ, unitTest r * q r ∂halfLineMeasure
  have ib : Integrable (fun r => unitTest r * q r) halfLineMeasure :=
    (unitTest_smooth.continuous.memLp_of_hasCompactSupport
      (p := 2) unitTest_compact).integrable_mul (Lp.memLp q)
  have tests (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
      (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioi (0 : ℝ)) :
      (∫ r : ℝ, g r * (q r - c) ∂halfLineMeasure) = 0 := by
    obtain ⟨a, ha, hga⟩ := lower_support_bound g hgs
    obtain ⟨R, hR, hgR⟩ := upper_support_bound g hgc
    let m : ℝ := ∫ r : ℝ, g r
    let h : ℝ → ℝ := fun r => g r - m * unitTest r
    have hhc : ContDiff ℝ 1 h :=
      (hg.sub (contDiff_const.mul unitTest_smooth)).of_le (by norm_num)
    have hmean : (∫ r : ℝ, h r) = 0 := by
      rw [show h = fun r => g r - m * unitTest r from rfl,
        integral_sub (hg.continuous.integrable_of_hasCompactSupport hgc)
          ((unitTest_smooth.continuous.integrable_of_hasCompactSupport unitTest_compact).const_mul m),
        integral_const_mul, unitTest_integral, mul_one]
      exact sub_self m
    obtain ⟨f, hf⟩ := zero_mean_core h hhc (min a (1 / 4)) (max R 1)
      (lt_min ha (by norm_num)) (hR.trans (le_max_left _ _))
      (by intro r hr; dsimp [h]; rw [hga r (hr.trans (min_le_left _ _)),
        unitTest_lower r (hr.trans (min_le_right _ _))]; ring)
      (by intro r hr; dsimp [h]; rw [hgR r ((le_max_left _ _).trans hr),
        unitTest_upper r ((le_max_right _ _).trans hr)]; ring) hmean
    have hzero := hq f
    rw [coordinate_pairing, hf] at hzero
    have ig : Integrable (fun r => g r * q r) halfLineMeasure :=
      (hg.continuous.memLp_of_hasCompactSupport (p := 2) hgc).integrable_mul (Lp.memLp q)
    have hsplit : (∫ r : ℝ, h r * q r ∂halfLineMeasure) =
        (∫ r : ℝ, g r * q r ∂halfLineMeasure) - m * c := by
      have he : (fun r => h r * q r) =
          (fun r => g r * q r - m * (unitTest r * q r)) := by
        funext r
        dsimp [h]
        ring
      rw [he, integral_sub ig (ib.const_mul m), integral_const_mul]
    rw [hsplit] at hzero
    have gim : Integrable g halfLineMeasure :=
      (hg.continuous.integrable_of_hasCompactSupport hgc).restrict
    have gm : (∫ r : ℝ, g r ∂halfLineMeasure) = m := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro r hr
      apply Function.notMem_support.mp
      intro hmem
      exact hr (hgs (subset_tsupport g hmem))
    have he : (fun r => g r * (q r - c)) =
        (fun r => g r * q r - g r * c) := by funext r; ring
    rw [he, integral_sub ig (gim.mul_const c), integral_mul_const, gm]
    nlinarith only [hzero]
  have hloc : LocallyIntegrable (fun r : ℝ => q r - c) halfLineMeasure :=
    ((Lp.memLp q).locallyIntegrable (by norm_num)).sub
      (continuous_const.locallyIntegrable : LocallyIntegrable (fun _ : ℝ => c) halfLineMeasure)
  have hdist := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := halfLineMeasure) hloc.locallyIntegrableOn
    (fun g hg hgc hgs => by simpa only [smul_eq_mul] using tests g hg hgc hgs)
  have heq : (q : ℝ → ℝ) =ᵐ[halfLineMeasure] (fun _ : ℝ => c) := by
    filter_upwards [hdist, ae_restrict_mem measurableSet_Ioi] with r hr hp
    exact sub_eq_zero.mp (hr hp)
  have hm : MemLp (fun _ : ℝ => c) 2 halfLineMeasure :=
    MemLp.ae_eq heq (Lp.memLp q)
  have hc : c = 0 := by
    have hh := (memLp_const_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp hm
    simpa [halfLineMeasure] using hh
  apply Lp.ext
  exact heq.trans (by simpa only [hc] using (Lp.coeFn_zero ℝ 2 halfLineMeasure).symm)

private def physicalCoordinateIsometry :
    PhysicalRadialEnergyCompletion →ₗᵢ[ℝ] FullRadialEnergyL2 where
  toLinearMap := physicalEnergyEmbedding.toLinearMap
  norm_map' := physicalEnergyCompletion_certified.2.2.2.1

private theorem embedding_surjective : Function.Surjective physicalEnergyEmbedding := by
  have horth : physicalEnergyEmbedding.rangeᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro q hq
    change q = 0
    apply annihilator_zero q
    intro f
    have hm : physicalCoreCoordinate f ∈ physicalEnergyEmbedding.range :=
      ⟨(f : PhysicalRadialEnergyCompletion), physicalEnergyCompletion_certified.2.2.1 f⟩
    exact (Submodule.mem_orthogonal.mp hq) _ hm
  have hclosed : IsClosed (physicalEnergyEmbedding.range : Set FullRadialEnergyL2) :=
    physicalCoordinateIsometry.isometry.isClosed_range
  have ht := Submodule.topologicalClosure_eq_top_iff.mpr horth
  rw [hclosed.submodule_topologicalClosure_eq] at ht
  exact LinearMap.range_eq_top.mp ht

/-- The proved physical-core energy equivalence, not a redefinition of L2. -/
def physicalEnergyEquivalence :
    PhysicalRadialEnergyCompletion ≃L[ℝ] FullRadialEnergyL2 :=
  ContinuousLinearEquiv.ofBijective physicalEnergyEmbedding
    (LinearMap.ker_eq_bot.mpr physicalEnergyCompletion_certified.2.2.2.2.1)
    (LinearMap.range_eq_top.mpr embedding_surjective)

/-- Actual inverse of the completed physical gradient coordinate. -/
def physicalEnergyLift : FullRadialEnergyL2 →L[ℝ] PhysicalRadialEnergyCompletion :=
  physicalEnergyEquivalence.symm.toContinuousLinearMap

private theorem lift_right (q : FullRadialEnergyL2) :
    physicalEnergyEmbedding (physicalEnergyLift q) = q :=
  physicalEnergyEquivalence.apply_symm_apply q

private theorem lift_left (u : PhysicalRadialEnergyCompletion) :
    physicalEnergyLift (physicalEnergyEmbedding u) = u :=
  physicalEnergyEquivalence.symm_apply_apply u

private theorem lift_norm (q : FullRadialEnergyL2) : ‖physicalEnergyLift q‖ = ‖q‖ := by
  rw [← physicalEnergyCompletion_certified.2.2.2.1, lift_right]

/-- R13: surjectivity, unique physical-completion representative, isometric
linear inverse and source-path transfer. No density or onto premise. -/
theorem physicalEnergySurjective_certified :
    Function.Surjective physicalEnergyEmbedding ∧
    (∀ q : FullRadialEnergyL2, ∃! u : PhysicalRadialEnergyCompletion,
      physicalEnergyEmbedding u = q) ∧
    (∀ q : FullRadialEnergyL2, physicalEnergyEmbedding (physicalEnergyLift q) = q) ∧
    (∀ u : PhysicalRadialEnergyCompletion, physicalEnergyLift (physicalEnergyEmbedding u) = u) ∧
    (∀ q : FullRadialEnergyL2, ‖physicalEnergyLift q‖ = ‖q‖) ∧
    (∀ q p : FullRadialEnergyL2, ‖physicalEnergyLift q - physicalEnergyLift p‖ = ‖q - p‖) ∧
    (∀ F : ℝ → FullRadialEnergyL2, ContDiff ℝ 1 F →
      ContDiff ℝ 1 (fun s => physicalEnergyLift (F s))) := by
  refine ⟨embedding_surjective, ?_, lift_right, lift_left, lift_norm, ?_, ?_⟩
  · intro q
    refine ⟨physicalEnergyLift q, lift_right q, ?_⟩
    intro u hu
    exact physicalEnergyCompletion_certified.2.2.2.2.1 (hu.trans (lift_right q).symm)
  · intro q p
    rw [← map_sub, lift_norm]
  · intro F hF
    exact physicalEnergyLift.contDiff.comp hF

end HBL.Modulation.Monopole
