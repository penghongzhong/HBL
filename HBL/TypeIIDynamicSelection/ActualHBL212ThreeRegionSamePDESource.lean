import HBL.TypeIIDynamicSelection.ActualOneLayerKummerSharedSource
import HBL.TypeIIDynamicSelection.ActualOneLayerInnerRemoteSource
import HBL.TypeIIDynamicSelection.ActualComplexMovingRemoteMatch
import Mathlib.Tactic

/-!
# Original 2.12: the SAME physical PDE forcing across H+, H-, Kummer and remote

For one actual nonterminal complex Hartree radiation Z, partition
  Z = Z_inner + Z_remote
with the genuine moving cutoff. No nonterminal support persistence
is assumed for Z. On a positive Kummer annulus inside the moving
core, the complete PDE source used by the previously constructed
Kummer Green inverse equals:

  F_K = (R(V+Z_inner)-R(V))
          + I_ext[|V+Z|^4-|V+Z_inner|^4] |V+Z_inner|^2 (V+Z_inner).

All terms come from the SAME original Hartree equation. The
outer interaction is the exact complex-background Riesz source,
not a real-surrogate cubic, and the two H+ and H- sources are
respectively the real/imaginary parts of F_K before restriction.

This result closes source-level three-domain consistency, NOT
the separate boundary-jet matching or the physical uniform
weighted source estimate and all positive generated orders.
Original prop:one-layer-stage3 is still OPEN.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- One actual Hartree PDE source, with its TRUE exterior Riesz
interaction, on the full chosen Kummer annulus inside a moving core. -/
theorem actual_Hartree_three_region_common_PDE_Kummer_source_exact
    {z d : ℝ}
    (V : ℝ → ℝ → ℝ) (R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega : ℝ → ℝ) (s : ℝ)
    (hRc : ContinuousAt R s)
    (hR : ∀ t, 0 < R t)
    (hcontinuous : Continuous (fun x : PhysicalAnnulus z d =>
      complexRadialRenormalizedResidual
        (fun t y => (V t y : ℂ) + Z t y) (b s) (omega s) s x.val -
      complexRadialRenormalizedResidual
        (fun t y => (V t y : ℂ)) (b s) (omega s) s x.val))
    (hAnnulusInCore : ∀ x : PhysicalAnnulus z d,
      0 < x.val ∧ 2 * x.val ≤ R s)
    (hUmeas : Measurable (actualOneLayerWithInnerRadiation V R Z s))
    (hQmeas : Measurable (actualOneLayerRemoteRadiation R Z s))
    (hF : IntegrableOn (actualMovingHartreeRemoteDensity V R Z s)
      (Ioi (R s)))
    (hUrow : ∀ x : PhysicalAnnulus z d,
      IntegrableOn (fun rho =>
        rho * hartreeRadialLog x.val rho *
        ‖actualOneLayerWithInnerRadiation V R Z s rho‖ ^ 4)
        (Ioi (0 : ℝ))) :
    ∀ x : PhysicalAnnulus z d,
      (actualHartreePDEResidualAnnulusSource
        V Z b omega s hcontinuous x) =
      actualOneLayerInnerCoreResidual V R Z (b s) (omega s) s x.val +
        (radialHartreeExteriorPotential
          (actualMovingHartreeRemoteDensity V R Z s)
          (R s) x.val : ℂ) *
        actualWholeRadiationLocalCubic
          (actualOneLayerWithInnerRadiation V R Z s) x.val := by
  intro x
  have hRemote :=
    actual_moving_physical_complex_remote_Riesz_exact
      V R Z (b s) (omega s) s x.val hRc hR
      (hAnnulusInCore x).1 (hAnnulusInCore x).2
      hUmeas hQmeas hF (hUrow x)
  change
    complexRadialRenormalizedResidual
      (actualOneLayerWithWholeRadiation V Z)
      (b s) (omega s) s x.val -
    complexRadialRenormalizedResidual
      (fun t y => (V t y : ℂ)) (b s) (omega s) s x.val =
    (complexRadialRenormalizedResidual
      (actualOneLayerWithInnerRadiation V R Z)
      (b s) (omega s) s x.val -
    complexRadialRenormalizedResidual
      (fun t y => (V t y : ℂ)) (b s) (omega s) s x.val) +
    (radialHartreeExteriorPotential
      (actualMovingHartreeRemoteDensity V R Z s)
      (R s) x.val : ℂ) *
      actualWholeRadiationLocalCubic
        (actualOneLayerWithInnerRadiation V R Z s) x.val
  rw [← hRemote]
  ring

end HBL.TypeIIDynamicSelection
