import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeMixedL1
import HBL.WeightedPhaseAffineSource
import HBL.MonopoleCoreIntegrability
import HBL.AffineTailLemmaClosed
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# Genuine whole-mixed Hartree source enters the ACTUAL weighted Fredholm space

The source is the real complete quartic Hartree density
F_ell = |V_c + Z_ell|^4 - |V_c|^4 - |Z_ell|^4
with the actual moment-generated V_c and fixed nonzero terminal radiation.

For each ell>0 and every real sigma, the full physical source belongs to
the true half-line L^(2,sigma) used by the H+ and H- Fredholm kernels.
Proof: physical compact support + genuine quartic pointwise bound,
and bounded continuous Japanese weight on that support.

This closes a real source-space *input* and does not assert that
both projected PDE channel sources are F_ell, nor that 2.12 has closed.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole
open HBL.Modulation.AffineTail HBL.L2Kernel

/-- The exact full physical mixed density enters the manuscript's
weighted L2 space, not a surrogate abstract data space. -/
theorem actual_one_orbit_Vc_whole_mixed_in_real_weighted_Fredholm
    (ell sigma : ℝ) (hell : 0 < ell) :
    InWeightedL2 sigma (actualOneOrbitVcWholeMixedQuartic ell) := by
  let F : ℝ → ℝ := actualOneOrbitVcWholeMixedQuartic ell
  let a : ℝ := 1 / (4 * ell)
  let b : ℝ := 4 / ell
  let M : ℝ :=
    4 * actualOneOrbitMovingEnvelope ^ 3 *
        ell ^ 3 * Real.sqrt ell +
      6 * actualOneOrbitMovingEnvelope ^ 2 * ell ^ 3 +
        4 * actualOneOrbitMovingEnvelope * ell ^ 2 * Real.sqrt ell
  have ha : 0 < a := by dsimp [a]; positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    have hb := actual_one_orbit_moving_envelope_pos
    positivity
  have hFmeas : Measurable F :=
    actual_one_orbit_Vc_whole_mixed_measurable ell
  have hsupp : Function.support F ⊆ Icc a b := by
    simpa only [F, a, b] using
      actual_one_orbit_Vc_whole_mixed_support ell hell
  have hcomp : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hFbound : ∀ r : ℝ, ‖F r‖ ≤ M := by
    intro r
    by_cases hr : r ∈ Icc a b
    · have hrpos : 0 < r := ha.trans_le hr.1
      simpa only [F, M, Real.norm_eq_abs] using
        actual_one_orbit_Vc_whole_mixed_pointwise_gain ell r hell hrpos
    · have hz : F r = 0 := by
        by_contra hn
        exact hr (hsupp hn)
      rw [hz, norm_zero]
      exact hM
  obtain ⟨K, hK⟩ :=
    hcomp.exists_bound_of_continuousOn
      (affineJapaneseWeight_continuous sigma).continuousOn
  have hQmeas : Measurable
      (fun r : ℝ => affineJapaneseWeight sigma r * F r) :=
    (affineJapaneseWeight_continuous sigma).measurable.mul hFmeas
  have hQcomp : HasCompactSupport
      (fun r : ℝ => affineJapaneseWeight sigma r * F r) :=
    hcomp.mul_left
  have hQbound : ∀ r : ℝ,
      ‖affineJapaneseWeight sigma r * F r‖ ≤ max K 0 * M := by
    intro r
    by_cases hr : r ∈ tsupport F
    · rw [norm_mul]
      exact mul_le_mul ((hK r hr).trans (le_max_left _ _))
        (hFbound r) (norm_nonneg _) (le_max_right _ _)
    · have hz : F r = 0 := image_eq_zero_of_notMem_tsupport hr
      rw [hz, mul_zero, norm_zero]
      exact mul_nonneg (le_max_right _ _) hM
  unfold InWeightedL2
  exact hQcomp.memLp_of_bound
    hQmeas.aestronglyMeasurable.restrict (max K 0 * M)
    (Filter.Eventually.of_forall hQbound)

end HBL.TypeIIDynamicSelection
