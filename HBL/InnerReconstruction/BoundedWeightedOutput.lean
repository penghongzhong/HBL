import HBL.InnerReconstruction.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem bounded_continuous_inWeightedL2_neg
    (tau : ℝ) (htau : 1 / 2 < tau) (q : ℝ → ℝ) (hq : Continuous q)
    (C : ℝ) (hC : ∀ r : ℝ, 0 < r → ‖q r‖ ≤ C) :
    InWeightedL2 (-tau) q := by
  have hmajor := (affineJapaneseDecay_memLp_two tau htau).const_mul C
  change MemLp (fun r => affineJapaneseDecay tau r * q r) 2 halfLineMeasure
  refine hmajor.mono' ((affineJapaneseDecay_continuous tau).mul hq).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hd : 0 ≤ affineJapaneseDecay tau r := by unfold affineJapaneseDecay; positivity
  rw [norm_mul, Real.norm_eq_abs (affineJapaneseDecay tau r), abs_of_nonneg hd]
  calc
    affineJapaneseDecay tau r * ‖q r‖ ≤ affineJapaneseDecay tau r * C :=
      mul_le_mul_of_nonneg_left (hC r hr) hd
    _ = _ := by ring
end HBL.Modulation.Monopole
