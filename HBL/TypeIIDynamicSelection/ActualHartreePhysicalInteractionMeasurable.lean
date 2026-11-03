import HBL.TypeIIDynamicSelection.ActualHartreeRieszMeasurability
import HBL.TypeIIDynamicSelection.ActualOneLayerRadiationPDECancellation
import Mathlib.Tactic

/-!
# Revised HBL 2.13: measurability of the SAME complete physical nonlocal Hartree source

The actual four-factor interaction has three genuine original inverse-square
radial Riesz potentials. For a measurable real core and a measurable
complex radiation field, the full source is measurable as a function of
the physical radial observation variable. This proof uses the existing
strictly developed measurable radial logarithmic Hartree integral,
never assumes source measurability separately and does not replace the
convolution with a local polynomial.

No rate, free matching coefficients or abstract regional inverse is used.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The original physical inverse-square Hartree nonlinear
bubble/radiation interaction is measurable on the same radial domain. -/
theorem actual_Hartree_physical_complete_interaction_measurable
    (V : ℝ → ℝ) (Z : ℝ → ℂ)
    (hV : Measurable V) (hZ : Measurable Z) :
    Measurable
      (fun r : ℝ => actualOneLayerInteractionOnly
        (fun _ : ℝ => V) (fun _ : ℝ => Z) 0 r) := by
  let vc : ℝ → ℂ := fun r => (V r : ℂ)
  let total : ℝ → ℂ := fun r => vc r + Z r
  let mix : ℝ → ℝ := actualWholeRadiationMixedQuartic V Z
  let pm : ℝ → ℝ := radialHartreePotential mix
  let pz : ℝ → ℝ := radialHartreePotential
    (fun rho => ‖Z rho‖ ^ 4)
  let pc : ℝ → ℝ := radialHartreePotential
    (fun rho => ‖vc rho‖ ^ 4)
  have hVc : Measurable vc := Complex.measurable_ofReal.comp hV
  have hTotal : Measurable total := hVc.add hZ
  have hMix : Measurable mix := by
    dsimp [mix,actualWholeRadiationMixedQuartic,total,vc]
    exact (((hVc.add hZ).norm.pow_const 4).sub
      (hVc.norm.pow_const 4)).sub (hZ.norm.pow_const 4)
  have hPm : Measurable pm :=
    actual_radialHartreePotential_measurable mix hMix
  have hPz : Measurable pz :=
    actual_radialHartreePotential_measurable
      (fun rho => ‖Z rho‖ ^ 4) (hZ.norm.pow_const 4)
  have hPc : Measurable pc :=
    actual_radialHartreePotential_measurable
      (fun rho => ‖vc rho‖ ^ 4) (hVc.norm.pow_const 4)
  have hCubic (u : ℝ → ℂ) (hu : Measurable u) :
      Measurable (fun r => actualWholeRadiationLocalCubic u r) := by
    unfold actualWholeRadiationLocalCubic
    exact (Complex.measurable_ofReal.comp
      (hu.norm.pow_const 2)).mul hu
  have hTotalC := hCubic total hTotal
  have hVcC := hCubic vc hVc
  have hZC := hCubic Z hZ
  have hPmC : Measurable (fun r => (pm r : ℂ)) :=
    Complex.measurable_ofReal.comp hPm
  have hPzC : Measurable (fun r => (pz r : ℂ)) :=
    Complex.measurable_ofReal.comp hPz
  have hPcC : Measurable (fun r => (pc r : ℂ)) :=
    Complex.measurable_ofReal.comp hPc
  have hSource : Measurable
      (fun r : ℝ =>
        (pm r : ℂ) * actualWholeRadiationLocalCubic total r +
        (pz r : ℂ) *
          (actualWholeRadiationLocalCubic total r -
            actualWholeRadiationLocalCubic Z r) +
        (pc r : ℂ) *
          (actualWholeRadiationLocalCubic total r -
            actualWholeRadiationLocalCubic vc r)) :=
    ((hPmC.mul hTotalC).add
      (hPzC.mul (hTotalC.sub hZC))).add
      (hPcC.mul (hTotalC.sub hVcC))
  change Measurable
    (fun r : ℝ =>
      (pm r : ℂ) * actualWholeRadiationLocalCubic total r +
      (pz r : ℂ) *
        (actualWholeRadiationLocalCubic total r -
          actualWholeRadiationLocalCubic Z r) +
      (pc r : ℂ) *
        (actualWholeRadiationLocalCubic total r -
          actualWholeRadiationLocalCubic vc r))
  exact hSource

end HBL.TypeIIDynamicSelection
