import HBL.TypeIIDynamicSelection.ActualHartreePhysicalFullWeightedL2
import HBL.TypeIIDynamicSelection.ActualOneLayerSingleComplexWeightedSource
import HBL.AffineTailCutoff

/-!
# Radially conjugated, genuinely localized physical Hartree inner forcing

The three-dimensional source F must become r*F under the radial
half-line conjugation u=r*w. Feeding F alone into the half-line
Fredholm inverse does not establish the physical PDE correspondence.

Here the original nonlocal F is retained, multiplied AFTER evaluating
its full Riesz interactions by r*(1-chi_aff(r/R)). The complementary
source is exactly r*chi_aff(r/R)*F; no nonlocal density is truncated.
The concrete smooth cutoff is one up to R and zero beyond 2R.

Taking R=ell^(-1/16) retains a positive ell^(1/16) weighted source gain,
without a time law for ell. Both physical forcing channels and their
forced affine Fredholm correction are then constructed, not assumed.
The common PDE's transport/phase terms, classical trace estimates,
outer matching and finite recursion remain separate open obligations.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

def actualHartreeSlowInnerRadius (ell : ℝ) : ℝ :=
  ell ^ (-(1 / 16 : ℝ))

def actualHartreeInnerSourceCutoff (R r : ℝ) : ℝ :=
  1 - cutoff (r / R)

def actualHartreeRadiallyConjugatedInnerSource
    (R ell c : ℝ) (z : ℝ → ℂ) (r : ℝ) : ℂ :=
  ((r * actualHartreeInnerSourceCutoff R r : ℝ) : ℂ) *
    actualHartreePhysicalSliceInteraction ell c z r

theorem actual_Hartree_inner_source_cutoff_continuous (R : ℝ) :
    Continuous (actualHartreeInnerSourceCutoff R) := by
  exact continuous_const.sub
    (cutoff_contDiff_infty.continuous.comp (continuous_id.div_const R))

theorem actual_Hartree_inner_source_cutoff_range (R r : ℝ) :
    0 ≤ actualHartreeInnerSourceCutoff R r ∧
      actualHartreeInnerSourceCutoff R r ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (r / R - 1)
  have h1 := Real.smoothTransition.le_one (r / R - 1)
  dsimp [actualHartreeInnerSourceCutoff, cutoff]
  constructor <;> linarith

theorem actual_Hartree_inner_source_cutoff_one
    (R r : ℝ) (hR : 0 < R) (hr : r ≤ R) :
    actualHartreeInnerSourceCutoff R r = 1 := by
  have hSmall : r / R ≤ 1 := (div_le_iff₀ hR).2 (by simpa using hr)
  unfold actualHartreeInnerSourceCutoff
  rw [cutoff_zero_of_le_one (r / R) hSmall]
  norm_num

/-- This is the genuine radial-conjugation multiplier, not a missing
factor absorbed into an unproved weighted-source hypothesis. -/
theorem actual_Hartree_inner_radial_multiplier_bound
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) :
    |r * actualHartreeInnerSourceCutoff R r| ≤ 2 * R := by
  obtain ⟨h0,h1⟩ := actual_Hartree_inner_source_cutoff_range R r
  by_cases hNear : r ≤ 2 * R
  · rw [abs_of_nonneg (mul_nonneg hr.le h0)]
    calc
      r * actualHartreeInnerSourceCutoff R r ≤ r * 1 :=
        mul_le_mul_of_nonneg_left h1 hr.le
      _ = r := mul_one _
      _ ≤ 2 * R := hNear
  · have hFar : 2 ≤ r / R :=
      (le_div_iff₀ hR).2 (le_of_lt (lt_of_not_ge hNear))
    have hZero : actualHartreeInnerSourceCutoff R r = 0 := by
      unfold actualHartreeInnerSourceCutoff
      rw [cutoff_one_of_two_le (r / R) hFar]
      ring
    rw [hZero, mul_zero, abs_zero]
    positivity

/-- Exact partition of the SAME conjugated full nonlocal interaction.
The exterior forcing is not dropped, and no cutoff is commuted through
any Hartree Riesz integral. -/
theorem actual_Hartree_conjugated_interaction_exact_partition
    (R ell c r : ℝ) (z : ℝ → ℂ) :
    (r : ℂ) * actualHartreePhysicalSliceInteraction ell c z r =
      actualHartreeRadiallyConjugatedInnerSource R ell c z r +
        ((r * cutoff (r / R) : ℝ) : ℂ) *
          actualHartreePhysicalSliceInteraction ell c z r := by
  unfold actualHartreeRadiallyConjugatedInnerSource actualHartreeInnerSourceCutoff
  push_cast
  ring

/-- The original source, with the necessary radial factor and actual
smooth inner partition, belongs to the genuine half-line weighted space.
The radius loss 2R is explicit. -/
theorem actual_Hartree_conjugated_localized_inner_weighted
    (R ell c B A : ℝ) (hR : 0 < R)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    Measurable (actualHartreeRadiallyConjugatedInnerSource R ell c z) ∧
    MemLp
      (fun r => affineJapaneseWeight (7 / 4 : ℝ) r *
        ‖actualHartreeRadiallyConjugatedInnerSource R ell c z r‖)
      2 halfLineMeasure ∧
    ∀ r : ℝ, 0 < r →
      affineJapaneseWeight (7 / 4 : ℝ) r *
        ‖actualHartreeRadiallyConjugatedInnerSource R ell c z r‖ ≤
      (2 * R) * (actualHartreePhysicalWeightedSourceConstant B A *
        ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ))) := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  let F : ℝ → ℂ := actualHartreePhysicalSliceInteraction ell c z
  let S : ℝ → ℝ := fun r => affineJapaneseWeight (7 / 4 : ℝ) r *
    ‖actualHartreeRadiallyConjugatedInnerSource R ell c z r‖
  have hV : Measurable V := actual_Hartree_moving_monopole_measurable c
  have hZ : Measurable Z := by
    dsimp [Z, rescalePhysicalRadiation]
    exact measurable_const.mul (hz.comp (measurable_const.mul measurable_id))
  have hF : Measurable F :=
    actual_Hartree_physical_complete_interaction_measurable V Z hV hZ
  have hCut : Measurable (actualHartreeInnerSourceCutoff R) :=
    (actual_Hartree_inner_source_cutoff_continuous R).measurable
  have hG : Measurable (actualHartreeRadiallyConjugatedInnerSource R ell c z) :=
    (Complex.measurable_ofReal.comp (measurable_id.mul hCut)).mul hF
  have hS : Measurable S :=
    (affineJapaneseWeight_continuous (7 / 4 : ℝ)).measurable.mul hG.norm
  have hS0 (r : ℝ) : 0 ≤ S r := by
    dsimp [S, affineJapaneseWeight]
    positivity
  have hDom (r : ℝ) (hr : 0 < r) :
      S r ≤ (2 * R) * (affineJapaneseWeight (7 / 4 : ℝ) r * ‖F r‖) := by
    have hCoeff := actual_Hartree_inner_radial_multiplier_bound R r hR hr
    have hW : 0 ≤ affineJapaneseWeight (7 / 4 : ℝ) r := by
      unfold affineJapaneseWeight
      positivity
    dsimp only [S, actualHartreeRadiallyConjugatedInnerSource]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ affineJapaneseWeight (7 / 4 : ℝ) r * ((2 * R) * ‖F r‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hCoeff (norm_nonneg _)) hW
      _ = _ := by ring
  have hRaw := (actual_Hartree_physical_full_interaction_weighted_L2
    B A ell c hB hA hell hellOne hc z hz hSup hStrauss).1
  have hMajor := hRaw.const_mul (2 * R)
  have hMem : MemLp S 2 halfLineMeasure := by
    apply hMajor.mono' hS.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (hS0 r)]
    exact hDom r hr
  refine ⟨hG, hMem, ?_⟩
  intro r hr
  exact (hDom r hr).trans (mul_le_mul_of_nonneg_left
    (actual_Hartree_physical_full_interaction_Japanese_pointwise
      ell c r B A hell hellOne hc hr hB hA z hz hSup hStrauss)
    (by positivity : 0 ≤ 2 * R))

/-- A scale-chosen inner radius absorbs the necessary radial factor
and retains strict positive LENGTH order 1/16. No time law is used. -/
theorem actual_Hartree_conjugated_slow_inner_one_sixteenth
    (ell c B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let G : ℝ → ℂ := actualHartreeRadiallyConjugatedInnerSource
      (actualHartreeSlowInnerRadius ell) ell c z
    Measurable G ∧
    MemLp (fun r => affineJapaneseWeight (7 / 4 : ℝ) r * ‖G r‖)
      2 halfLineMeasure ∧
    ∀ r : ℝ, 0 < r →
      affineJapaneseWeight (7 / 4 : ℝ) r * ‖G r‖ ≤
      (2 * actualHartreePhysicalWeightedSourceConstant B A) *
        ell ^ (1 / 16 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) := by
  let R : ℝ := actualHartreeSlowInnerRadius ell
  have hR : 0 < R := Real.rpow_pos_of_pos hell _
  have hBase := actual_Hartree_conjugated_localized_inner_weighted
    R ell c B A hR hell hellOne hc hB hA z hz hSup hStrauss
  have hPower : R * ell ^ (1 / 8 : ℝ) = ell ^ (1 / 16 : ℝ) := by
    dsimp [R, actualHartreeSlowInnerRadius]
    rw [← Real.rpow_add hell]
    norm_num
  refine ⟨hBase.1, hBase.2.1, ?_⟩
  intro r hr
  calc
    _ ≤ (2 * R) * (actualHartreePhysicalWeightedSourceConstant B A *
        ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ))) := hBase.2.2 r hr
    _ = (2 * actualHartreePhysicalWeightedSourceConstant B A) *
        (R * ell ^ (1 / 8 : ℝ)) * (1 + r) ^ (-(5 / 8 : ℝ)) := by ring
    _ = _ := by rw [hPower]

/-- Correct half-line inner forcing: r times a concrete smooth piece
of the SAME physical nonlocal interaction. Weighted membership and
compatibility are outputs, not assumptions. -/
theorem actual_Hartree_conjugated_slow_inner_unique_solve
    (ell c B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let G : ℝ → ℂ := actualHartreeRadiallyConjugatedInnerSource
      (actualHartreeSlowInnerRadius ell) ell c z
    let gp : ℝ → ℝ := fun r => (G r).re
    let gm : ℝ → ℝ := fun r => (G r).im
    ∃ (hp : InWeightedL2 (7 / 4 : ℝ) gp)
      (hm : InWeightedL2 (7 / 4 : ℝ) gm),
      AffineTailOrthogonal HartreeChannel.plus gp (actualPlusCharge gp) ∧
      AffineTailOrthogonal HartreeChannel.minus gm (actualMinusCharge gm) ∧
      ∃! x : InnerCorrections,
        (1 - weightedBirmanSchwingerOperator)
            (x.1 : RealL2 halfLineMeasure) =
          weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
            (weightedSourceDataL2 (7 / 4 : ℝ) (correctedPlusSource gp)
              (correctedPlusSource_memWeightedL2 (7 / 4 : ℝ)
                (by norm_num) gp hp)) ∧
        (1 - weightedPhaseBirman)
            (x.2 : RealL2 halfLineMeasure) =
          weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
            (weightedSourceDataL2 (7 / 4 : ℝ) (correctedMinusSource gm)
              (correctedMinusSource_memWeightedL2 (7 / 4 : ℝ)
                (by norm_num) gm hm)) := by
  let G : ℝ → ℂ := actualHartreeRadiallyConjugatedInnerSource
    (actualHartreeSlowInnerRadius ell) ell c z
  let gp : ℝ → ℝ := fun r => (G r).re
  let gm : ℝ → ℝ := fun r => (G r).im
  have hBase := actual_Hartree_conjugated_slow_inner_one_sixteenth
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hPair := actual_Hartree_one_complex_weighted_source_two_channels
    (7 / 4 : ℝ) G hBase.1 hBase.2.1
  have hp : InWeightedL2 (7 / 4 : ℝ) gp := hPair.1
  have hm : InWeightedL2 (7 / 4 : ℝ) gm := hPair.2
  have hPairing : (1 / 2 : ℝ) < 7 / 4 := by norm_num
  refine ⟨hp, hm,
    actualPlusCharge_orthogonal (7 / 4 : ℝ) hPairing gp hp,
    actualMinusCharge_orthogonal (7 / 4 : ℝ) hPairing gm hm, ?_⟩
  exact existsUnique_actualInner_affinelyCorrected
    (7 / 4 : ℝ) (by norm_num) (by norm_num) gp gm hp hm

end HBL.TypeIIDynamicSelection
