import HBL.TypeIIDynamicSelection.ActualHartreeStraussRieszEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeNonlocalWeightedQuantitative
import HBL.TypeIIDynamicSelection.ActualHartreeMomentRadiusWindow
import Mathlib.Tactic

/-!
# Genuine 3D Hartree quartic NONLOCAL source in its ORIGINAL weighted Fredholm norm

Use only the published Strauss radial Sobolev estimate, the standard
high-regularity Hartree flow's L-infinity bound, and the exact physical
moving radius R=4/(kappa_H*ell*m0(z)).
Unlike a separate abstract source-order assumption, Lean proves that
these explicit H1/Linfty hypotheses imply the precise quartic Riesz
envelope and hence a QUANTITATIVE L^(2,sigma)(0,infty) commutator norm.

The only PDE-flow inputs are real physical positive moments and
pointwise radial Sobolev representative bounds. In particular the full
Hartree Riesz kernel, critical sqrt(ell) radiation and true nonlocal
truncation are unchanged.

This eliminates a previously freely postulated decay hypothesis but
does not assume/prove the global Kummer/remote matching or Type II rate.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- No separate |z|^4 ≤ D*W^2 hypothesis: Strauss + uniform
physical H^L-infinity implies full nonlocal cutoff weighted-L2 gain. -/
theorem actual_Hartree_true_radiation_weighted_Riesz_from_Strauss
    (ell R B A sigma : ℝ)
    (hell : 0 < ell) (hR : 0 < R)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hSigmaLo : 3 / 2 < sigma) (hSigmaHi : sigma < 2)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    (eLpNorm
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualHartreeNonlocalCutoffError R ell z r‖)
      2 halfLineMeasure).toReal ≤
      (affineJapaneseWeight sigma (2 * R) *
        ((2 * radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4)) * B ^ 3) *
          ell ^ 2 * Real.sqrt ell)) * Real.sqrt (2 * R) := by
  have hD : 0 ≤ (2 * (B ^ 4 + A ^ 4)) := by positivity
  exact actual_Hartree_nonlocal_physical_weighted_L2_quantitative
    ell R B (2 * (B ^ 4 + A ^ 4)) sigma
    hell hR hB hD hSigmaLo hSigmaHi z hz hSup
    (actual_Hartree_radial_quartic_envelope_from_Strauss
      z B A hB hA hSup hStrauss)

/-- For one actual radial Hartree orbit, the moving cutoff radius
is determined by the original full physical inverse-square quartic
moment, NOT prescribed as an independent gluing parameter. -/
theorem actual_Hartree_one_orbit_moving_weighted_Riesz_from_Strauss
    (ell m B A sigma : ℝ)
    (hell : 0 < ell) (hm : 0 < m)
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
      (affineJapaneseWeight sigma
          (2 * actualHartreeMomentCutoffRadius ell m) *
        ((2 * radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4)) * B ^ 3) *
          ell ^ 2 * Real.sqrt ell)) *
        Real.sqrt (2 * actualHartreeMomentCutoffRadius ell m) := by
  have hR : 0 < actualHartreeMomentCutoffRadius ell m := by
    have hk : 0 < hartreeKappa := by
      unfold hartreeKappa
      positivity
    unfold actualHartreeMomentCutoffRadius
    positivity
  exact actual_Hartree_true_radiation_weighted_Riesz_from_Strauss
    ell (actualHartreeMomentCutoffRadius ell m) B A sigma
    hell hR hB hA hSigmaLo hSigmaHi z hz hSup hStrauss

end HBL.TypeIIDynamicSelection
