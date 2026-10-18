import HBL.WeightedScaleResonance
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
Nontriviality of the concrete weighted scaling resonance in half-line L2.

The proof uses the continuous representative and its already verified
nonzero value at radius `1 / 2`.  No spectral classification or Fredholm
solution is imported, so this file can be used upstream of both bridges.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

theorem weightedScaleResonance_half_ne_zero :
    weightedScaleResonance (1 / 2 : ℝ) ≠ 0 := by
  rw [weightedScaleResonance_closed]
  exact mul_ne_zero (inv_ne_zero (by positivity))
    radialResonancePlus_half_ne_zero

/-- The weighted scaling mode is a nonzero vector of the actual half-line
L2 space, rather than merely a nonzero pointwise representative. -/
theorem weightedScaleResonanceL2_ne_zero :
    weightedScaleResonanceL2 ≠ 0 := by
  intro hzero
  have hae : weightedScaleResonance =ᵐ[halfLineMeasure]
      (0 : ℝ → ℝ) := by
    have hrepr := weightedScaleResonanceL2_ae
    rw [hzero] at hrepr
    exact hrepr.symm.trans (Lp.coeFn_zero ℝ 2 halfLineMeasure)
  have hpoint := Measure.eqOn_open_of_ae_eq (μ := volume) hae isOpen_Ioi
    weightedScaleResonance_continuous.continuousOn
    continuous_zero.continuousOn
  exact weightedScaleResonance_half_ne_zero (hpoint (by norm_num))

/-- The span appearing in the fixed-space classification has dimension
exactly one. -/
theorem weightedScaleResonanceL2_span_finrank :
    Module.finrank ℝ (Submodule.span ℝ {weightedScaleResonanceL2}) = 1 :=
  finrank_span_singleton weightedScaleResonanceL2_ne_zero

end HBL.Modulation.Monopole
