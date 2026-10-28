import HBL.InnerEstimates.WeightedNormIdentity
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerWeightedNorm_le_of_bound (tau : ℝ) (htau : 1 / 2 < tau)
    (q : ℝ → ℝ) (hq : Continuous q) (C : ℝ)
    (hC : ∀ r : ℝ, 0 < r → ‖q r‖ ≤ C) :
    innerWeightedNorm (-tau) q ≤ innerDecayNorm tau htau * C := by
  have hqmem := bounded_continuous_inWeightedL2_neg tau htau q hq C hC
  rw [innerWeightedNorm_eq (-tau) q hqmem, mul_comm (innerDecayNorm tau htau) C]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedSourceDataL2_ae (-tau) q hqmem,
    (affineJapaneseDecay_memLp_two tau htau).coeFn_toLp,
    ae_restrict_mem measurableSet_Ioi] with r hq' hd' hr
  rw [hq', hd']
  change ‖affineJapaneseDecay tau r * q r‖ ≤ C * ‖affineJapaneseDecay tau r‖
  rw [norm_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC r hr) (norm_nonneg _)
end HBL.Modulation.Monopole
