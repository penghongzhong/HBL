import HBL.TestedHamiltonCoupling.NormalizedProfileDefinitions
noncomputable section
set_option autoImplicit false
open Filter
open scoped ContDiff Topology
namespace HBL.MainBackward
open HBL.Modulation

theorem normalizedHamiltonTest_profiles :
    ContDiff ℝ 2 normalizedPhaseTestProfile ∧
    (∀ r, radialU normalizedPhaseTestProfile r = normalizedZetaMinus r) ∧
    (∀ r, Real.exp 1 ≤ r → normalizedPhaseTestProfile r = 0) ∧
    normalizedZetaPlus 0 = 0 ∧
    normalizedZetaPlus (Real.exp 1) = 0 ∧
    deriv normalizedZetaPlus (Real.exp 1) = 0 := by
  have hR : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  refine ⟨?_, ?_, ?_, normalizedZetaPlus_zero_of_nonpos 0 le_rfl,
    normalizedZetaPlus_zero_of_one_le _ hR.le, ?_⟩
  · unfold normalizedPhaseTestProfile
    exact (contDiff_const.mul (thresholdBump.contDiff.mul bubble_contDiff_infty)).of_le
      (by simp)
  · intro r
    unfold radialU normalizedPhaseTestProfile normalizedZetaMinus radialResonanceMinus
    ring
  · intro r hr
    simp [normalizedPhaseTestProfile, thresholdBump_zero_of_one_le r (hR.le.trans hr)]
  · have he : normalizedZetaPlus =ᶠ[𝓝 (Real.exp 1)] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hR] with r hr
      exact normalizedZetaPlus_zero_of_one_le r hr.le
    exact ((hasDerivAt_const (Real.exp 1) (0 : ℝ)).congr_of_eventuallyEq he).deriv
end HBL.MainBackward
