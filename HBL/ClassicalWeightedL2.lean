import HBL.WeightedFreeGreenPointwise
import Mathlib.Topology.Order.Compact

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

theorem classical_halfLine_norm_bounded_of_tendsto
    (h : ℝ → ℝ) {d : ℝ}
    (hh : ContinuousOn h (Ici (0 : ℝ)))
    (hlim : Tendsto h atTop (𝓝 d)) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → ‖h r‖ ≤ C := by
  have hevent : ∀ᶠ r in atTop, ‖h r‖ < ‖d‖ + 1 :=
    (tendsto_order.mp hlim.norm).2 (‖d‖ + 1) (by linarith)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hevent
  have hcompact : ContinuousOn (fun r => ‖h r‖) (Icc (0 : ℝ) R) :=
    (hh.mono Icc_subset_Ici_self).norm
  obtain ⟨A, hA⟩ := isCompact_Icc.bddAbove_image hcompact
  refine ⟨max A (‖d‖ + 1), ?_⟩
  intro r hr
  by_cases hrR : r ≤ R
  · exact (hA (mem_image_of_mem _ ⟨hr, hrR⟩)).trans (le_max_left _ _)
  · exact (hR r (lt_of_not_ge hrR).le).le.trans (le_max_right _ _)

theorem classical_weighted_memLp_two_of_bound
    (h : ℝ → ℝ) (hh : ContinuousOn h (Ici (0 : ℝ)))
    (C : ℝ) (hC : ∀ r : ℝ, 0 ≤ r → ‖h r‖ ≤ C) :
    MemLp (fun r => weightedGreenDecay r * h r) 2 halfLineMeasure := by
  have hcont : ContinuousOn (fun r => weightedGreenDecay r * h r) (Ioi (0 : ℝ)) :=
    weightedGreenDecay_continuous.continuousOn.mul (hh.mono Ioi_subset_Ici_self)
  have hmeas : AEStronglyMeasurable (fun r => weightedGreenDecay r * h r)
      halfLineMeasure := hcont.aestronglyMeasurable measurableSet_Ioi
  apply (weightedGreenDecay_memLp_two.const_mul C).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (weightedGreenDecay_nonneg r)]
  calc
    weightedGreenDecay r * ‖h r‖ ≤ weightedGreenDecay r * C :=
      mul_le_mul_of_nonneg_left (hC r hr.le) (weightedGreenDecay_nonneg r)
    _ = C * weightedGreenDecay r := mul_comm _ _

/-- Classical continuity at the origin and a finite far-field limit place
the actual weighted remainder in the concrete half-line L2 space. -/
theorem classical_weighted_memLp_two_of_tendsto
    (h : ℝ → ℝ) {d : ℝ}
    (hh : ContinuousOn h (Ici (0 : ℝ)))
    (hlim : Tendsto h atTop (𝓝 d)) :
    MemLp (fun r => weightedGreenDecay r * h r) 2 halfLineMeasure := by
  obtain ⟨C, hC⟩ := classical_halfLine_norm_bounded_of_tendsto h hh hlim
  exact classical_weighted_memLp_two_of_bound h hh C hC

def classicalWeightedL2 (h : ℝ → ℝ) {d : ℝ}
    (hh : ContinuousOn h (Ici (0 : ℝ)))
    (hlim : Tendsto h atTop (𝓝 d)) : RealL2 halfLineMeasure :=
  (classical_weighted_memLp_two_of_tendsto h hh hlim).toLp
    (fun r => weightedGreenDecay r * h r)

theorem classicalWeightedL2_ae (h : ℝ → ℝ) {d : ℝ}
    (hh : ContinuousOn h (Ici (0 : ℝ)))
    (hlim : Tendsto h atTop (𝓝 d)) :
    (classicalWeightedL2 h hh hlim : ℝ → ℝ) =ᵐ[halfLineMeasure]
      fun r => weightedGreenDecay r * h r :=
  (classical_weighted_memLp_two_of_tendsto h hh hlim).coeFn_toLp

end HBL.Modulation.Monopole
