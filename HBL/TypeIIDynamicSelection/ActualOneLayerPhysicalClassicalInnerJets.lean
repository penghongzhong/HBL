import HBL.TypeIIDynamicSelection.ActualOneLayerSingleComplexWeightedSource
import HBL.InnerReconstruction.ActualClassicalAffineSolution
import Mathlib.Tactic

/-!
# Original 2.12: classical H+/H- boundary jets from ONE actual Hartree PDE

Previously the physical two-channel inverse was represented in weighted
L2, whose elements have no pointwise boundary trace. Here the
already strictly verified physical Green reconstruction provides actual
C2 classical *function* representatives up(r), um(r) with their forced
real affine threshold charges, origin normalization and exact original
H+/H- nonlocal differential equations.

Critically F+ = Re R_PDE and F- = Im R_PDE derive from the
SAME complex Hartree residual: one complex weighted L2 source norm
and its actual continuity yield BOTH classical inner corrections.
This removes the false inference "weighted L2 solution has a trace".
The boundary values and derivatives used for Kummer matching are now
well-defined; EQUALITY to the Kummer jets is not assumed nor proved.

The full original 2.12 region-jet matching and strict generated-order
estimates remain OPEN. No paper-original acceptance is claimed.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- Classical positive-radius two-channel physical Hartree source jets,
with their actual forced affine charges and original equations. -/
theorem actual_Hartree_one_PDE_source_has_classical_Hplus_Hminus_jets
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s : ℝ)
    (hCont : Continuous
      (actualOneLayerCommonPDEResidual V Z b omega s))
    (hComplexWeighted : MemLp
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualOneLayerCommonPDEResidual V Z b omega s r‖)
      2 halfLineMeasure) :
    ∃ up um : ℝ → ℝ,
      InnerAffineProperties up
        (actualPlusCharge (actualOneLayerPlusPDE V Z b omega s)) ∧
      InnerAffineProperties um
        (actualMinusCharge (actualOneLayerMinusPDE V Z b omega s)) ∧
      ∀ r : ℝ, 0 < r →
        DifferentiableAt ℝ up r ∧
        DifferentiableAt ℝ (deriv up) r ∧
        DifferentiableAt ℝ um r ∧
        DifferentiableAt ℝ (deriv um) r ∧
        hPlusApply up r = actualOneLayerPlusPDE V Z b omega s r ∧
        hMinusApply um r = actualOneLayerMinusPDE V Z b omega s r := by
  have hPair :=
    actual_Hartree_one_complex_weighted_source_two_channels
      sigma (actualOneLayerCommonPDEResidual V Z b omega s)
      hCont.measurable hComplexWeighted
  have hp : Continuous (actualOneLayerPlusPDE V Z b omega s) := by
    change Continuous (fun r : ℝ =>
      (actualOneLayerCommonPDEResidual V Z b omega s r).re)
    exact Complex.continuous_re.comp hCont
  have hm : Continuous (actualOneLayerMinusPDE V Z b omega s) := by
    change Continuous (fun r : ℝ =>
      (actualOneLayerCommonPDEResidual V Z b omega s r).im)
    exact Complex.continuous_im.comp hCont
  obtain ⟨_x,up,um,_hplusAE,_hminusAE,hPlus,hMinus,hClassical⟩ :=
    exists_actualInner_classical_affine
      sigma hLower hUpper
      (actualOneLayerPlusPDE V Z b omega s)
      (actualOneLayerMinusPDE V Z b omega s)
      hPair.1 hPair.2 hp hm
  exact ⟨up,um,hPlus,hMinus,hClassical⟩

end HBL.TypeIIDynamicSelection
