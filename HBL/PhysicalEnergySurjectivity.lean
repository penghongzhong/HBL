import HBL.PhysicalEnergyCompletion
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
R13: the actual compact radial gradient core has dense derivative coordinates.
An annihilator is constant by smooth compact tests, and the infinite half-line
has no nonzero constant L2 vector. Completeness then makes the existing
isometric embedding onto. No density, surjectivity or inverse is assumed.
This does not identify the L6/weak-gradient realization or the 3D nonlocal form.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem cutoffDerivative_smooth : ContDiff ℝ ∞ (deriv cutoff) :=
  (contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).2

private theorem cutoffDerivative_support : HasCompactSupport (deriv cutoff) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2))
  intro r hr
  by_contra h
  have hc : deriv cutoff r = 0 := by
    have hout : r < 1 ∨ 2 < r := by
      by_cases hleft : r < 1
      · exact Or.inl hleft
      · exact Or.inr (lt_of_not_ge (fun hright => h ⟨le_of_not_gt hleft, hright⟩))
    rcases hout with hleft | hright
    · have he : cutoff =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
        filter_upwards [Iio_mem_nhds hleft] with t ht
        exact cutoff_zero_of_le_one t ht.le
      rw [he.deriv_eq]
      exact deriv_const r 0
    · have he : cutoff =ᶠ[𝓝 r] (fun _ => (1 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds hright] with t ht
        exact cutoff_one_of_two_le t ht.le
      rw [he.deriv_eq]
      exact deriv_const r 1
  exact hr hc

private theorem halfLine_integral_cap (g : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ t, R < t → g t = 0) :
    (∫ t, g t ∂halfLineMeasure) = ∫ t in (0 : ℝ)..R, g t := by
  change (∫ t in Ioi (0 : ℝ), g t) = _
  rw [intervalIntegral.integral_of_le hR]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc (0 : ℝ) R ⊆ Ioi (0 : ℝ) from fun _ ht => ht.1)
  intro t ht
  apply hz
  by_contra h
  exact ht.2 ⟨ht.1, le_of_not_gt h⟩

/-- Removing the mass by one fixed smooth transition produces an actual
compact radial core, not a postulated derivative range element. -/
private theorem corrected_test_is_core
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ∃ f : PhysicalGradientCore,
      (physicalCoreCoordinate f : ℝ → ℝ) =ᵐ[halfLineMeasure]
        (fun r => g r - (∫ t, g t ∂halfLineMeasure) * deriv cutoff r) := by
  let C : ℝ := ∫ t, g t ∂halfLineMeasure
  let G : ℝ → ℝ := fun r => (∫ t in (0 : ℝ)..r, g t) - C * cutoff r
  have hG (r : ℝ) : HasDerivAt G (g r - C * deriv cutoff r) r := by
    have hi := intervalIntegral.integral_hasDerivAt_right
      (hg.continuous.intervalIntegrable 0 r)
      hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuous.continuousAt
    exact hi.sub (((contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).1 r).hasDerivAt.const_mul C)
  have hder : deriv G = fun r => g r - C * deriv cutoff r :=
    funext fun r => (hG r).deriv
  have hGs : ContDiff ℝ ∞ G := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun r => (hG r).differentiableAt, ?_⟩
    rw [hder]
    exact hg.sub (contDiff_const.mul cutoffDerivative_smooth)
  have hG0 : G 0 = 0 := by simp [G, cutoff_zero_of_le_one 0 (by norm_num)]
  have hgn : {r : ℝ | g r = 0} ∈ 𝓝 (0 : ℝ) := by
    have h0 : (0 : ℝ) ∉ tsupport g := fun h => (lt_irrefl (0 : ℝ)) (hgp h)
    filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds h0] with r hr
    exact image_eq_zero_of_notMem_tsupport hr
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp hgn
  have hGnear : ∀ r : ℝ, |r| < min δ 1 → G r = 0 := by
    intro r hr
    have hi : (∫ t in (0 : ℝ)..r, g t) = 0 := by
      calc
        (∫ t in (0 : ℝ)..r, g t) = ∫ _t in (0 : ℝ)..r, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          apply hsmall
          rw [Metric.mem_ball, Real.dist_eq, sub_zero]
          have hab : |t| ≤ |r| := by
            rcases le_total 0 r with hr0 | hr0
            · rw [uIcc_of_le hr0] at ht
              rw [abs_of_nonneg ht.1, abs_of_nonneg hr0]
              exact ht.2
            · rw [uIcc_of_ge hr0] at ht
              rw [abs_of_nonpos ht.2, abs_of_nonpos hr0]
              exact neg_le_neg ht.1
          exact hab.trans_lt (hr.trans_le (min_le_left _ _))
        _ = 0 := by simp
    have hr1 : r ≤ 1 := (le_abs_self r).trans (hr.le.trans (min_le_right _ _))
    simp only [G, hi, cutoff_zero_of_le_one r hr1, mul_zero, sub_zero]
  let f : ℝ → ℝ := fun r => G r / r
  have hfs : ContDiff ℝ 1 f := by
    apply contDiff_iff_contDiffAt.mpr
    intro r
    by_cases hr : r = 0
    · subst r
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show 0 < min δ 1 from lt_min hδ zero_lt_one)] with t ht
      change G t / t = 0
      rw [hGnear t (by simpa [Metric.mem_ball, Real.dist_eq] using ht), zero_div]
    · exact (hGs.of_le (by norm_num)).contDiffAt.div contDiffAt_id hr
  obtain ⟨M, hM⟩ := hgc.isCompact.bddAbove
  let R : ℝ := max 2 (M + 1)
  have hR2 : 2 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := by linarith
  have hfcut : ∀ r : ℝ, R ≤ r → f r = 0 := by
    intro r hr
    have hz : ∀ t : ℝ, r < t → g t = 0 := by
      intro t ht
      apply image_eq_zero_of_notMem_tsupport
      intro hts
      have hb := hM hts
      have hRM : M + 1 ≤ R := le_max_right _ _
      linarith
    have hi := halfLine_integral_cap g r (hR0.trans hr) hz
    change ((∫ t in (0 : ℝ)..r, g t) - C * cutoff r) / r = 0
    rw [← hi, cutoff_one_of_two_le r (hR2.trans hr)]
    simp [C]
  let core : PhysicalGradientCore := ⟨f, hfs, R, hR0, hfcut⟩
  have hU : radialU (core : ℝ → ℝ) = G := by
    funext r
    change r * (G r / r) = G r
    by_cases hr : r = 0
    · simp [hr, hG0]
    · field_simp
  refine ⟨core, ?_⟩
  have he : (physicalCoreCoordinate core : ℝ → ℝ) =ᵐ[halfLineMeasure]
      deriv (radialU (core : ℝ → ℝ)) := smoothToRadialDotH1_ae _ _
  rw [hU, hder] at he
  exact he

private theorem core_range_orthogonal_zero (h : FullRadialEnergyL2)
    (hh : h ∈ physicalCoreCoordinate.rangeᗮ) : h = 0 := by
  have hl : LocallyIntegrable (h : ℝ → ℝ) halfLineMeasure :=
    (Lp.memLp h).locallyIntegrable (by norm_num)
  have hb : Integrable (fun r => deriv cutoff r * h r) halfLineMeasure := by
    simpa only [smul_eq_mul] using
      hl.integrable_smul_left_of_hasCompactSupport cutoffDerivative_smooth.continuous
        cutoffDerivative_support
  let c : ℝ := ∫ r, deriv cutoff r * h r ∂halfLineMeasure
  have hpair (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
      (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
      (∫ r, g r * h r ∂halfLineMeasure) = (∫ r, g r ∂halfLineMeasure) * c := by
    obtain ⟨f, hf⟩ := corrected_test_is_core g hg hgc hgp
    have hz : inner ℝ (physicalCoreCoordinate f) h = 0 :=
      hh _ ⟨f, rfl⟩
    have hi : (∫ r, (g r - (∫ t, g t ∂halfLineMeasure) * deriv cutoff r) * h r
        ∂halfLineMeasure) = 0 := by
      rw [L2.inner_def] at hz
      convert hz using 1
      apply integral_congr_ae
      filter_upwards [hf] with r hr
      rw [hr, Real.inner_apply]
    have hgprod : Integrable (fun r => g r * h r) halfLineMeasure := by
      simpa only [smul_eq_mul] using
        hl.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
    have heq : (fun r => (g r - (∫ t, g t ∂halfLineMeasure) * deriv cutoff r) * h r) =
        (fun r => g r * h r - (∫ t, g t ∂halfLineMeasure) * (deriv cutoff r * h r)) := by
      funext r
      ring
    rw [heq, integral_sub hgprod (hb.const_mul _), integral_const_mul] at hi
    exact sub_eq_zero.mp hi
  have hdiff : LocallyIntegrable (fun r : ℝ => h r - c) halfLineMeasure :=
    hl.sub continuous_const.locallyIntegrable
  have hae : ∀ᵐ r ∂halfLineMeasure, h r = c := by
    have hzero := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hdiff.locallyIntegrableOn (Ioi (0 : ℝ))) (fun g hg hgc hgp => by
        have hgprod : Integrable (fun r => g r * h r) halfLineMeasure := by
          simpa only [smul_eq_mul] using
            hl.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
        have hgint : Integrable g halfLineMeasure := hg.continuous.integrable_of_hasCompactSupport hgc
        simp only [smul_eq_mul, mul_sub]
        rw [integral_sub hgprod (hgint.mul_const c), integral_mul_const, hpair g hg hgc hgp,
          sub_self])
    filter_upwards [hzero, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
    exact sub_eq_zero.mp (hr hrpos)
  have hcLp : MemLp (fun _ : ℝ => c) 2 halfLineMeasure := MemLp.ae_eq hae (Lp.memLp h)
  have hc0 : c = 0 := by
    rcases (memLp_const_iff (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)).mp hcLp with hc | hfinite
    · exact hc
    · have hinf : halfLineMeasure Set.univ = ⊤ := by
        simp [halfLineMeasure]
      rw [hinf] at hfinite
      exact (lt_irrefl _ hfinite).elim
  apply Lp.ext
  filter_upwards [hae, Lp.coeFn_zero ℝ 2 halfLineMeasure] with r hr hz
  simp only [hr, hc0, hz, Pi.zero_apply]

private theorem core_range_dense : DenseRange physicalCoreCoordinate := by
  have ho : physicalCoreCoordinate.rangeᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro h hh
    exact (Submodule.mem_bot ℝ).mpr (core_range_orthogonal_zero h hh)
  have hd : physicalCoreCoordinate.range.topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr ho
  change Dense (Set.range physicalCoreCoordinate)
  rw [dense_iff_closure_eq]
  exact congrArg (fun M : Submodule ℝ FullRadialEnergyL2 => (M : Set FullRadialEnergyL2)) hd

/-- The original physical-gradient coordinate map, now as a linear isometry. -/
def physicalEnergyLinearIsometry : PhysicalRadialEnergyCompletion →ₗᵢ[ℝ] FullRadialEnergyL2 where
  toLinearMap := physicalEnergyEmbedding.toLinearMap
  norm_map' := physicalEnergyCompletion_certified.2.2.2.1

private theorem embedding_surjective : Function.Surjective physicalEnergyEmbedding := by
  have hc : IsClosed (Set.range physicalEnergyEmbedding) :=
    physicalEnergyLinearIsometry.isometry.isClosedEmbedding.isClosed_range
  have hsub : Set.range physicalCoreCoordinate ⊆ Set.range physicalEnergyEmbedding := by
    rintro _ ⟨f, rfl⟩
    exact ⟨(f : PhysicalRadialEnergyCompletion), physicalEnergyCompletion_certified.2.2.1 f⟩
  have hcl := closure_minimal hsub hc
  rw [core_range_dense.closure_range] at hcl
  intro q
  exact hcl (Set.mem_univ q)

/-- Constructed onto isometry from the physical core completion to all half-line L2. -/
def physicalEnergyEquiv : PhysicalRadialEnergyCompletion ≃ₗᵢ[ℝ] FullRadialEnergyL2 :=
  LinearIsometryEquiv.ofSurjective physicalEnergyLinearIsometry embedding_surjective

/-- One full R13 environment: actual core density, onto isometry, unique
physical completion representative and a bounded linear inverse, with no
new assumptions on the source or on the range. -/
theorem physicalEnergySurjectivity_certified :
    DenseRange physicalCoreCoordinate ∧
    Function.Surjective physicalEnergyEmbedding ∧
    (∀ q : FullRadialEnergyL2, ∃! u : PhysicalRadialEnergyCompletion,
      physicalEnergyEmbedding u = q) ∧
    (∀ u : PhysicalRadialEnergyCompletion, physicalEnergyEquiv u = physicalEnergyEmbedding u) ∧
    (∀ q : FullRadialEnergyL2, physicalEnergyEmbedding (physicalEnergyEquiv.symm q) = q) ∧
    (∀ q : FullRadialEnergyL2, ‖physicalEnergyEquiv.symm q‖ = ‖q‖) := by
  refine ⟨core_range_dense, embedding_surjective, ?_, (fun _ => rfl), ?_, ?_⟩
  · intro q
    refine ⟨physicalEnergyEquiv.symm q, physicalEnergyEquiv.apply_symm_apply q, ?_⟩
    intro u hu
    apply physicalEnergyCompletion_certified.2.2.2.2.1
    exact hu.trans (physicalEnergyEquiv.apply_symm_apply q).symm
  · exact physicalEnergyEquiv.apply_symm_apply
  · exact physicalEnergyEquiv.symm.norm_map

end HBL.Modulation.Monopole
