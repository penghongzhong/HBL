import HBL.TypeIIDynamicSelection.ActualHartreePhysicalFullWeightedL2
import HBL.TypeIIDynamicSelection.ActualOneLayerSingleComplexWeightedSource

/-!
# Actual Hartree interaction to the original two-channel inner inverse

The forcing is the complete original nonlocal interaction of the moving
monopole and one critically rescaled physical radiation field. Its two
weighted real channels, their forced affine charges, compatibility, and
unique Fredholm correction are CONCLUSIONS of physical radiation bounds.
No weighted-source hypothesis, freely chosen charge, or solvability
assumption is introduced.

Scope: the interaction contribution to the inner correction only. This
is not the entire common PDE residual (transport and modulation remain),
not a classical interface trace theorem, and not a three-region matching
or finite-profile existence theorem. Manuscript 2.13 remains open.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- Both actual inner forcing channels have the original weighted
half-line membership, derived solely from the physical radiation data. -/
theorem actual_Hartree_physical_interaction_inner_channels
    (ell c B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    InWeightedL2 (7 / 4 : ℝ)
        (fun r => (actualHartreePhysicalSliceInteraction ell c z r).re) ∧
      InWeightedL2 (7 / 4 : ℝ)
        (fun r => (actualHartreePhysicalSliceInteraction ell c z r).im) := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  have hV : Measurable V := actual_Hartree_moving_monopole_measurable c
  have hZ : Measurable Z := by
    dsimp [Z, rescalePhysicalRadiation]
    exact measurable_const.mul
      (hz.comp (measurable_const.mul measurable_id))
  have hF : Measurable (actualHartreePhysicalSliceInteraction ell c z) :=
    actual_Hartree_physical_complete_interaction_measurable V Z hV hZ
  have hWeighted :=
    (actual_Hartree_physical_full_interaction_weighted_L2
      ell c B A hell hellOne hc hB hA z hz hSup hStrauss).1
  exact actual_Hartree_one_complex_weighted_source_two_channels
    (7 / 4 : ℝ) (actualHartreePhysicalSliceInteraction ell c z) hF hWeighted

/-- The original inner Fredholm correction exists uniquely for this
same physical Hartree interaction. Both affine charges are forced by
its actual resonance pairings; compatibility is proved, not assumed. -/
theorem actual_Hartree_physical_interaction_inner_solve_from_radiation
    (ell c B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let gp : ℝ → ℝ :=
      fun r => (actualHartreePhysicalSliceInteraction ell c z r).re
    let gm : ℝ → ℝ :=
      fun r => (actualHartreePhysicalSliceInteraction ell c z r).im
    ∃ (hp : InWeightedL2 (7 / 4 : ℝ) gp)
      (hm : InWeightedL2 (7 / 4 : ℝ) gm),
      AffineTailOrthogonal HartreeChannel.plus gp (actualPlusCharge gp) ∧
      AffineTailOrthogonal HartreeChannel.minus gm (actualMinusCharge gm) ∧
      channelPairing HartreeChannel.plus (correctedPlusSource gp) = 0 ∧
      channelPairing HartreeChannel.minus (correctedMinusSource gm) = 0 ∧
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
  let gp : ℝ → ℝ :=
    fun r => (actualHartreePhysicalSliceInteraction ell c z r).re
  let gm : ℝ → ℝ :=
    fun r => (actualHartreePhysicalSliceInteraction ell c z r).im
  have hPair := actual_Hartree_physical_interaction_inner_channels
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hp : InWeightedL2 (7 / 4 : ℝ) gp := hPair.1
  have hm : InWeightedL2 (7 / 4 : ℝ) gm := hPair.2
  have hPairing : (1 / 2 : ℝ) < 7 / 4 := by norm_num
  have hCompatible := actualAffine_corrected_sources_compatible
    (7 / 4 : ℝ) hPairing gp gm hp hm
  refine ⟨hp, hm,
    actualPlusCharge_orthogonal (7 / 4 : ℝ) hPairing gp hp,
    actualMinusCharge_orthogonal (7 / 4 : ℝ) hPairing gm hm,
    hCompatible.1, hCompatible.2, ?_⟩
  exact existsUnique_actualInner_affinelyCorrected
    (7 / 4 : ℝ) (by norm_num) (by norm_num) gp gm hp hm

end HBL.TypeIIDynamicSelection
