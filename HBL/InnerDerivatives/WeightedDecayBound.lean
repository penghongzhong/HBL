import HBL.InnerDerivatives.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerWeightedNorm_le_of_inverse_linear_bound (beta : ℝ) (hbeta : beta < 1 / 2)
    (q : ℝ → ℝ) (hq : AEStronglyMeasurable q halfLineMeasure) (C : ℝ)
    (hC : ∀ r : ℝ, 0 < r → (1 + r) * ‖q r‖ ≤ C) :
    InWeightedL2 beta q ∧ innerWeightedNorm beta q ≤ innerDecayNorm (1 - beta) (by linarith) * C := by
  have hpoint (r : ℝ) (hr : 0 < r) :
      ‖affineJapaneseWeight beta r * q r‖ ≤ C * affineJapaneseDecay (1 - beta) r := by
    have hw : affineJapaneseWeight beta r = affineJapaneseDecay (1 - beta) r * affineJapaneseWeight 1 r := by
      unfold affineJapaneseWeight affineJapaneseDecay
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + r ^ 2)]
      congr 1
      ring
    have h1 : affineJapaneseWeight 1 r ≤ 1 + r := by
      rw [affineJapaneseWeight, ← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    have hd : 0 ≤ affineJapaneseDecay (1 - beta) r := by unfold affineJapaneseDecay; positivity
    rw [norm_mul, Real.norm_of_nonneg (by unfold affineJapaneseWeight; positivity), hw, mul_assoc]
    calc
      _ ≤ affineJapaneseDecay (1 - beta) r * ((1 + r) * ‖q r‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) hd
      _ ≤ affineJapaneseDecay (1 - beta) r * C := mul_le_mul_of_nonneg_left (hC r hr) hd
      _ = _ := mul_comm _ _
  have hmem : InWeightedL2 beta q := by
    apply ((affineJapaneseDecay_memLp_two (1 - beta) (by linarith)).const_mul C).mono'
      ((affineJapaneseWeight_continuous beta).aestronglyMeasurable.mul hq)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hpoint r hr
  refine ⟨hmem, ?_⟩
  rw [innerWeightedNorm_eq beta q hmem, mul_comm (innerDecayNorm _ _) C]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedSourceDataL2_ae beta q hmem,
    (affineJapaneseDecay_memLp_two (1 - beta) (by linarith)).coeFn_toLp,
    ae_restrict_mem measurableSet_Ioi] with r hq' hd' hr
  rw [hq', hd', Real.norm_of_nonneg (show 0 ≤ affineJapaneseDecay (1 - beta) r by unfold affineJapaneseDecay; positivity)]
  exact hpoint r hr
end HBL.Modulation.Monopole
