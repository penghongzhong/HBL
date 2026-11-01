import HBL.TypeIIDynamicSelection.ActualOneLayerTwoChannelPDE
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# One actual complex Hartree source controls BOTH physical Fredholm channels

The exact Hartree PDE produces one common complex residual. Its H+ and
H- parts are real and imaginary projections of that same residual.
Rather than postulating two unrelated weighted source estimates, it
suffices to prove a SINGLE weighted L2 estimate for its complex
magnitude. The real/imaginary estimates then follow from
|Re z| <= norm z and |Im z| <= norm z.

This is an exact functional-analytic bridge. The source majorant
is visible as a hypothesis, not assumed small or source-free; verifying
it from the actual selected off-terminal PDE orbit and proving the
Kummer/remote positive-order estimates are still open.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Modulation.AffineTail
open HBL.Modulation.Monopole
open HBL.Profile.ActualInner
open HBL.L2Kernel

/-- ONE complex weighted source bound automatically supplies both
genuine real- and phase-channel physical Fredholm source bounds.
The magnitudes and weights use the original half-line measure. -/
theorem actual_Hartree_one_complex_weighted_source_two_channels
    (sigma : ℝ) (F : ℝ → ℂ)
    (hFmeas : Measurable F)
    (hF : MemLp (fun r : ℝ => affineJapaneseWeight sigma r * ‖F r‖)
      2 halfLineMeasure) :
    InWeightedL2 sigma (fun r => (F r).re) ∧
    InWeightedL2 sigma (fun r => (F r).im) := by
  have hWeight (r : ℝ) : 0 ≤ affineJapaneseWeight sigma r := by
    unfold affineJapaneseWeight
    positivity
  have hReMeas : Measurable (fun r : ℝ => (F r).re) :=
    Complex.continuous_re.measurable.comp hFmeas
  have hImMeas : Measurable (fun r : ℝ => (F r).im) :=
    Complex.continuous_im.measurable.comp hFmeas
  have hReAES : AEStronglyMeasurable
      (fun r : ℝ => affineJapaneseWeight sigma r * (F r).re)
      halfLineMeasure :=
    (((affineJapaneseWeight_continuous sigma).measurable.mul hReMeas).aestronglyMeasurable.restrict)
  have hImAES : AEStronglyMeasurable
      (fun r : ℝ => affineJapaneseWeight sigma r * (F r).im)
      halfLineMeasure :=
    (((affineJapaneseWeight_continuous sigma).measurable.mul hImMeas).aestronglyMeasurable.restrict)
  constructor
  · change MemLp (fun r : ℝ => affineJapaneseWeight sigma r * (F r).re)
      2 halfLineMeasure
    apply hF.mono' hReAES
    filter_upwards with r
    simpa only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hWeight r), abs_of_nonneg (norm_nonneg (F r))] using
      (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm (F r))
        (hWeight r))
  · change MemLp (fun r : ℝ => affineJapaneseWeight sigma r * (F r).im)
      2 halfLineMeasure
    apply hF.mono' hImAES
    filter_upwards with r
    simpa only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hWeight r), abs_of_nonneg (norm_nonneg (F r))] using
      (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm (F r))
        (hWeight r))

/-- From one SINGLE actual physical Hartree PDE residual weighted
norm, recover both unique actual affine threshold charges. -/
theorem actual_Hartree_common_PDE_one_weighted_norm_unique_charges
    (sigma : ℝ) (hSigma : 3 / 2 < sigma)
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s : ℝ)
    (hSourceMeas : Measurable
      (actualOneLayerCommonPDEResidual V Z b omega s))
    (hSourceWeighted : MemLp
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualOneLayerCommonPDEResidual V Z b omega s r‖)
      2 halfLineMeasure) :
    ∃! charges : ℝ × ℝ,
      AffineTailOrthogonal HartreeChannel.plus
        (actualOneLayerPlusPDE V Z b omega s) charges.1 ∧
      AffineTailOrthogonal HartreeChannel.minus
        (actualOneLayerMinusPDE V Z b omega s) charges.2 := by
  obtain ⟨hp, hm⟩ :=
    actual_Hartree_one_complex_weighted_source_two_channels sigma
      (actualOneLayerCommonPDEResidual V Z b omega s)
      hSourceMeas hSourceWeighted
  exact actual_one_layer_common_PDE_unique_affine_charges
    sigma hSigma V Z b omega s hp hm

/-- The SAME single complex physical Hartree PDE weighted source estimate
produces the unique H+/H- pair of normalized weighted Fredholm
corrections; no independently chosen second source is introduced. -/
theorem actual_Hartree_common_PDE_one_weighted_norm_unique_inner
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s : ℝ)
    (hSourceMeas : Measurable
      (actualOneLayerCommonPDEResidual V Z b omega s))
    (hSourceWeighted : MemLp
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualOneLayerCommonPDEResidual V Z b omega s r‖)
      2 halfLineMeasure) :
    ∃! x : InnerCorrections,
      (1 - weightedBirmanSchwingerOperator)
          (x.1 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator sigma (by linarith)
          (weightedSourceDataL2 sigma
            (correctedPlusSource (actualOneLayerPlusPDE V Z b omega s))
            (correctedPlusSource_memWeightedL2 sigma hUpper.le
              (actualOneLayerPlusPDE V Z b omega s)
              (actual_Hartree_one_complex_weighted_source_two_channels
                sigma (actualOneLayerCommonPDEResidual V Z b omega s)
                hSourceMeas hSourceWeighted).1)) ∧
      (1 - weightedPhaseBirman)
          (x.2 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator sigma (by linarith)
          (weightedSourceDataL2 sigma
            (correctedMinusSource (actualOneLayerMinusPDE V Z b omega s))
            (correctedMinusSource_memWeightedL2 sigma hUpper.le
              (actualOneLayerMinusPDE V Z b omega s)
              (actual_Hartree_one_complex_weighted_source_two_channels
                sigma (actualOneLayerCommonPDEResidual V Z b omega s)
                hSourceMeas hSourceWeighted).2)) := by
  obtain ⟨hp, hm⟩ :=
    actual_Hartree_one_complex_weighted_source_two_channels sigma
      (actualOneLayerCommonPDEResidual V Z b omega s)
      hSourceMeas hSourceWeighted
  exact actual_one_layer_common_PDE_unique_inner_solutions
    sigma hLower hUpper V Z b omega s hp hm

end HBL.TypeIIDynamicSelection
