import HBL.TypeIIDynamicSelection.ActualHartreePhysicalFullWeightedL2
import HBL.TypeIIDynamicSelection.ActualHartreeCriticalNonlinearityScaling
import HBL.TypeIIDynamicSelection.ActualOneLayerSingleComplexWeightedSource
import Mathlib.Tactic

/-!
# The actual dynamically phased physical Hartree interaction is in the original source space

This module is a thin reuse bridge.  It does not re-estimate any Riesz
potential or any of the ten nonlinear monomials.  A unit complex phase is
absorbed into the physical radiation slice and the already proved complete
weighted source theorem is called verbatim.

This is the source-space interface needed to connect the genuine phased
physical flow to the two normalized Fredholm channels.  No Kummer matching,
finite recursion, or Type-II rate is asserted here.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- The same physical interaction, with the genuine unit dynamical phase
placed in the radiation before critical rescaling. -/
def actualHartreePhasedPhysicalSliceInteraction
    (ell c gamma : ℝ) (z : ℝ → ℂ) : ℝ → ℂ :=
  actualHartreePhysicalSliceInteraction ell c
    (fun u => actualHartreeUnitPhase gamma * z u)

/-- Critical rescaling commutes exactly with the frozen unit phase. -/
theorem actual_Hartree_phased_rescale_eq
    (ell gamma : ℝ) (z : ℝ → ℂ) :
    rescalePhysicalRadiation ell
        (fun u => actualHartreeUnitPhase gamma * z u) =
      fun r => actualHartreeUnitPhase gamma *
        rescalePhysicalRadiation ell z r := by
  funext r
  unfold rescalePhysicalRadiation
  ring

/-- Hence the definition above is literally the interaction of the real
monopole with the dynamically phased rescaled physical radiation. -/
theorem actual_Hartree_phased_physical_slice_interaction_eq
    (ell c gamma : ℝ) (z : ℝ → ℂ) :
    actualHartreePhasedPhysicalSliceInteraction ell c gamma z =
      fun r => actualOneLayerInteractionOnly
        (fun _ : ℝ =>
          monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c)
        (fun _ : ℝ => fun x =>
          actualHartreeUnitPhase gamma *
            rescalePhysicalRadiation ell z x) 0 r := by
  unfold actualHartreePhasedPhysicalSliceInteraction
    actualHartreePhysicalSliceInteraction
  rw [actual_Hartree_phased_rescale_eq]

/-- The already certified complete interaction estimate survives the true
unit phase with exactly the same constant and the same ell^(1/8) gain. -/
theorem actual_Hartree_phased_physical_full_interaction_weighted_L2
    (B A ell c gamma : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    MemLp
      (fun r : ℝ => affineJapaneseWeight (7 / 4 : ℝ) r *
        ‖actualHartreePhasedPhysicalSliceInteraction ell c gamma z r‖)
      2 halfLineMeasure ∧
    (∫ r in Ioi (0 : ℝ),
      (affineJapaneseWeight (7 / 4 : ℝ) r *
        ‖actualHartreePhasedPhysicalSliceInteraction ell c gamma z r‖) ^ 2) ≤
      (actualHartreePhysicalWeightedSourceConstant B A) ^ 2 *
        ell ^ (1 / 4 : ℝ) *
        (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 4 : ℝ))) := by
  let zp : ℝ → ℂ := fun u => actualHartreeUnitPhase gamma * z u
  have hzp : Measurable zp := measurable_const.mul hz
  have hSupP : ∀ u : ℝ, 0 < u → ‖zp u‖ ≤ B := by
    intro u hu
    dsimp [zp]
    rw [norm_mul, actual_Hartree_unit_phase_norm, one_mul]
    exact hSup u hu
  have hStraussP : ∀ u : ℝ, 1 ≤ u → u * ‖zp u‖ ≤ A := by
    intro u hu
    dsimp [zp]
    rw [norm_mul, actual_Hartree_unit_phase_norm, one_mul]
    exact hStrauss u hu
  simpa only [actualHartreePhasedPhysicalSliceInteraction, zp] using
    (actual_Hartree_physical_full_interaction_weighted_L2
      B A ell c hB hA hell hellOne hc zp hzp hSupP hStraussP)

/-- The same one complex phased source therefore gives both genuine
threshold channels in the original L^(2,7/4) source space. -/
theorem actual_Hartree_phased_physical_interaction_two_channels
    (B A ell c gamma : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    InWeightedL2 (7 / 4 : ℝ)
      (fun r => (actualHartreePhasedPhysicalSliceInteraction
        ell c gamma z r).re) ∧
    InWeightedL2 (7 / 4 : ℝ)
      (fun r => (actualHartreePhasedPhysicalSliceInteraction
        ell c gamma z r).im) := by
  let zp : ℝ → ℂ := fun u => actualHartreeUnitPhase gamma * z u
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell zp
  have hzp : Measurable zp := measurable_const.mul hz
  have hZ : Measurable Z := by
    dsimp [Z, rescalePhysicalRadiation]
    exact measurable_const.mul
      (hzp.comp (measurable_const.mul measurable_id))
  have hV := actual_Hartree_moving_monopole_measurable c
  have hSource : Measurable
      (actualHartreePhasedPhysicalSliceInteraction ell c gamma z) := by
    change Measurable
      (fun r : ℝ => actualOneLayerInteractionOnly
        (fun _ : ℝ => V) (fun _ : ℝ => Z) 0 r)
    exact actual_Hartree_physical_complete_interaction_measurable V Z hV hZ
  have hLp :=
    (actual_Hartree_phased_physical_full_interaction_weighted_L2
      B A ell c gamma hB hA hell hellOne hc z hz hSup hStrauss).1
  exact actual_Hartree_one_complex_weighted_source_two_channels
    (7 / 4 : ℝ)
    (actualHartreePhasedPhysicalSliceInteraction ell c gamma z)
    hSource hLp

end HBL.TypeIIDynamicSelection
