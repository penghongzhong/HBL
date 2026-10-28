import HBL.InnerReconstruction.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem weightedSource_momentWeight_memLp
    (sigma : ℝ) (hsigma : 3 / 2 < sigma) :
    MemLp (fun r : ℝ => r * affineJapaneseDecay sigma r) 2 halfLineMeasure := by
  have hc : Continuous (fun r : ℝ => r * affineJapaneseDecay sigma r) :=
    continuous_id.mul (affineJapaneseDecay_continuous sigma)
  have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 * (sigma - 1) := by
    rw [Module.finrank_self]; norm_num; linarith
  have hmajor : Integrable (fun r : ℝ => (1 + r ^ 2) ^ (-(sigma - 1))) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hdim
    simp only [Real.norm_eq_abs, sq_abs] at h
    convert h using 1
    funext r
    congr 1
    ring
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable.restrict).2
  refine hmajor.integrableOn.mono' (hc.pow 2).aestronglyMeasurable.restrict ?_
  filter_upwards with r
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow,
    affineJapaneseDecay_sq]
  calc
    r ^ 2 * (1 + r ^ 2) ^ (-sigma) ≤
        (1 + r ^ 2) * (1 + r ^ 2) ^ (-sigma) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _)
    _ = (1 + r ^ 2) ^ (-(sigma - 1)) := by
      calc
        _ = (1 + r ^ 2) ^ (1 : ℝ) * (1 + r ^ 2) ^ (-sigma) := by
          rw [Real.rpow_one]
        _ = _ := by
          rw [← Real.rpow_add (by positivity)]
          congr 1
          ring
end HBL.Modulation.Monopole
