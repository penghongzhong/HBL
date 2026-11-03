import HBL.TypeIIDynamicSelection.ActualHartreePhysicalFullWeightedL2
import HBL.TypeIIDynamicSelection.ActualOneLayerSingleComplexWeightedSource
import Mathlib.Tactic

/-!
# Actual physical Hartree source to the two normalized inner Fredholm equations

This instantiates the original two-channel inverse with the SAME complete
core-radiation interaction whose spatial weighted L2 bound is proved.
The input is only the physical radiation measurability, amplitude and
Strauss bounds, together with the core/scale parameter range. Source
measurability, source-space membership, compatibility and free affine
slopes are NOT additional hypotheses.

Both affine slopes are uniquely forced by physical resonance pairings.
The conclusion is a Hilbert-space inner correction; it does not assert
pointwise traces, C1 Kummer matching, a complete iterated PDE residual,
positive dynamical time order or Type-II blowup.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- Measurability of the actual moving-core, physically scaled source. -/
theorem actual_Hartree_physical_slice_source_measurable
    (ell c : ℝ) (z : ℝ → ℂ) (hz : Measurable z) :
    Measurable (actualHartreePhysicalSliceInteraction ell c z) := by
  have hV : Measurable
      (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c) :=
    actual_Hartree_moving_monopole_measurable c
  have hZ : Measurable (rescalePhysicalRadiation ell z) := by
    unfold rescalePhysicalRadiation
    exact measurable_const.mul (hz.comp (measurable_const.mul measurable_id))
  exact actual_Hartree_physical_complete_interaction_measurable
    (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c)
    (rescalePhysicalRadiation ell z) hV hZ

/-- Both physical channel sources are derived from one actual complex
interaction. Neither channel weighted norm is assumed. -/
theorem actual_Hartree_physical_source_two_weighted_channels
    (B A ell c : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    InWeightedL2 (7 / 4 : ℝ)
      (fun r => (actualHartreePhysicalSliceInteraction ell c z r).re) ∧
    InWeightedL2 (7 / 4 : ℝ)
      (fun r => (actualHartreePhysicalSliceInteraction ell c z r).im) := by
  exact actual_Hartree_one_complex_weighted_source_two_channels
    (7 / 4 : ℝ) (actualHartreePhysicalSliceInteraction ell c z)
    (actual_Hartree_physical_slice_source_measurable ell c z hz)
    (actual_Hartree_physical_full_interaction_weighted_L2
      B A ell c hB hA hell hellOne hc z hz hSup hStrauss).1

/-- From physical radiation input alone: uniquely forced real affine
charges, exact zero-charge compatibility, and one unique normalized
pair solving the ORIGINAL H+/H- weighted Fredholm equations.

The existential hp,hm are proved memberships, not hypotheses. They are
exposed only to type the genuine source-data L2 realizations. -/
theorem actual_Hartree_physical_source_unique_affine_inner_correction
    (B A ell c : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let Fp : ℝ → ℝ :=
      fun r => (actualHartreePhysicalSliceInteraction ell c z r).re
    let Fm : ℝ → ℝ :=
      fun r => (actualHartreePhysicalSliceInteraction ell c z r).im
    ∃ hp : InWeightedL2 (7 / 4 : ℝ) Fp,
    ∃ hm : InWeightedL2 (7 / 4 : ℝ) Fm,
      (∃! a : ℝ × ℝ,
        AffineTailOrthogonal HartreeChannel.plus Fp a.1 ∧
        AffineTailOrthogonal HartreeChannel.minus Fm a.2) ∧
      channelPairing HartreeChannel.plus (correctedPlusSource Fp) = 0 ∧
      channelPairing HartreeChannel.minus (correctedMinusSource Fm) = 0 ∧
      (∃! x : InnerCorrections,
        (1 - weightedBirmanSchwingerOperator)
            (x.1 : RealL2 halfLineMeasure) =
          weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
            (weightedSourceDataL2 (7 / 4 : ℝ)
              (correctedPlusSource Fp)
              (correctedPlusSource_memWeightedL2 (7 / 4 : ℝ)
                (by norm_num) Fp hp)) ∧
        (1 - weightedPhaseBirman)
            (x.2 : RealL2 halfLineMeasure) =
          weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
            (weightedSourceDataL2 (7 / 4 : ℝ)
              (correctedMinusSource Fm)
              (correctedMinusSource_memWeightedL2 (7 / 4 : ℝ)
                (by norm_num) Fm hm))) := by
  dsimp only
  let Fp : ℝ → ℝ :=
    fun r => (actualHartreePhysicalSliceInteraction ell c z r).re
  let Fm : ℝ → ℝ :=
    fun r => (actualHartreePhysicalSliceInteraction ell c z r).im
  obtain ⟨hp, hm⟩ := actual_Hartree_physical_source_two_weighted_channels
    B A ell c hB hA hell hellOne hc z hz hSup hStrauss
  have hCompat := actualAffine_corrected_sources_compatible
    (7 / 4 : ℝ) (by norm_num) Fp Fm hp hm
  refine ⟨hp, hm, ?_, hCompat.1, hCompat.2, ?_⟩
  · exact existsUnique_actual_twoChannel_affine_charges
      (7 / 4 : ℝ) (by norm_num) (by norm_num) Fp Fm hp hm
  · exact existsUnique_actualInner_affinelyCorrected
      (7 / 4 : ℝ) (by norm_num) (by norm_num) Fp Fm hp hm

end HBL.TypeIIDynamicSelection
