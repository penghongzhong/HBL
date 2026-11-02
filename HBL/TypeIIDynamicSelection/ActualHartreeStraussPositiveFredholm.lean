import HBL.TypeIIDynamicSelection.ActualHartreeWeightedPositiveOrder
import HBL.TypeIIDynamicSelection.ActualHartreeStraussRieszEnvelope
import Mathlib.Tactic

/-!
# Real original Hartree 2.12 Fredholm order from cited radial Sobolev theory

This is the direct same-PDE synthesis of TWO independently
strict-certified results. The source is the full inverse-square
quartic Riesz commutator on the moment-selected physical cutoff.
The true L^(2,sigma) order 2-sigma>0 is DEDUCED, not assigned.

The quartic Riesz source envelope is no longer an additional premise:
it follows in Lean from the classical Strauss radial H1 pointwise
bound, the standard high-regularity L-infinity estimate, and the
physical all-radiation moment lower bound.

The actual terminal orbit's m0 lower bound was proved in
ActualOneOrbitPhysicalTerminalRadiusWindow. The literature input
for H1/Linfinity radial flow must be connected to the physical
solution's pointwise representative. This lemma does NOT close
the nonlinear Vc+Z mixed source or Kummer/Frobenius matching, so
the original 2.12 remains OPEN.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual Hartree Riesz source is quantitatively small in
the ORIGINAL Fredholm weighted L2 space, with NO independent
quartic-density decay hypothesis and with strictly positive order. -/
theorem actual_Hartree_radial_Strauss_true_Fredholm_positive_gain
    (ell m m0 B A sigma : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hm0 : 0 < m0) (hm0m : m0 ≤ m)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hSigmaLo : 3 / 2 < sigma) (hSigmaHi : sigma < 2)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    (eLpNorm
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualHartreeNonlocalCutoffError
          (actualHartreeMomentCutoffRadius ell m) ell z r‖)
        2 halfLineMeasure).toReal ≤
      ((2 * radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4)) * B ^ 3) *
        ((1 + (2 * (4 / (hartreeKappa * m0))) ^ 2) ^
          (sigma / 2) *
           Real.sqrt (2 * (4 / (hartreeKappa * m0))))) *
        ell ^ (2 - sigma) := by
  have hD : 0 ≤ 2 * (B ^ 4 + A ^ 4) := by positivity
  exact actual_Hartree_physical_nonlocal_Riesz_positive_Fredholm_gain
    ell m m0 B (2 * (B ^ 4 + A ^ 4)) sigma
    hell hellOne hm0 hm0m hB hD hSigmaLo hSigmaHi z hz
    hSup
    (actual_Hartree_radial_quartic_envelope_from_Strauss
      z B A hB hA hSup hStrauss)

end HBL.TypeIIDynamicSelection
