import HBL.TypeIIDynamicSelection.ActualHartreePhysicalInnerKummerBridge
import HBL.TypeIIDynamicSelection.ActualHartreePhasedPhysicalFlowPDE
import HBL.TypeIIDynamicSelection.ActualOneLayerRadiationPDECancellation
import Mathlib.Tactic

/-!
# Revised HBL 2.13: real physical Hartree flow forces the actual interaction-only source

This bridge eliminates the independent 'radiation PDE = 0' premise
from the earlier Hartree bubble/radiation interaction formula.
The SAME real high-regularity 3D radial Hartree trajectory is
critically rescaled with the genuine physical clock and complex phase.
The original complete nonlocal renormalized PDE is then derived,
and all its pure-radiation evolution terms cancel from the common
H+/H- source. The remainder is the COMPLETE nonlinear inverse-square
Hartree interaction, not an abstract source or surrogate polynomial.

Physical spacetime regularity, the actual original physical Hartree
PDE, and three radial Riesz integrability requirements remain visible.
No Type-II blowup law or smallness of the interaction is assumed.
This is a supporting source identity, not revised manuscript 2.13.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The original physical Hartree PDE, the actual clock/scale and
the forced dynamic phase turn the common two-channel PDE residual
into precisely the FULL Hartree bubble-radiation interaction.
No independent renormalized-radiation-PDE assumption occurs. -/
theorem actual_Hartree_physical_flow_forces_common_interaction_source
    (V : ℝ → ℝ → ℝ)
    (ell time b gamma : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ) (s r gs : ℝ)
    (hell : 0 < ell s) (hr : 0 < r)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hClock : HasDerivAt time ((ell s) ^ 2) s)
    (hGamma : HasDerivAt gamma gs s)
    (L : (ℝ × ℝ) →L[ℝ] ℂ) (zt zr : ℂ)
    (hJoint : HasFDerivAt (fun p : ℝ × ℝ => z p.1 p.2) L
      (time s, ell s * r))
    (hJac : ∀ a c : ℝ,
      L (a,c) = (a : ℂ) * zt + (c : ℂ) * zr)
    (hzSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (z (time s)) (ell s * x))
    (hzSecond : DifferentiableAt ℝ (deriv (z (time s))) (ell s * r))
    (hzDeriv : deriv (z (time s)) (ell s * r) = zr)
    (hPhysicalPDE :
      Complex.I * zt +
        complexRadialLaplacian (z (time s)) (ell s * r) +
        complexRadialHartreeNonlinearity (z (time s)) (ell s * r) = 0)
    (hVTime : DifferentiableAt ℝ
      (fun t : ℝ => (V t r : ℂ)) s)
    (hZTime : DifferentiableAt ℝ
      (fun t : ℝ => actualHartreePhasedScaledRadiation z ell time gamma t r) s)
    (hVSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (fun y => (V s y : ℂ)) x)
    (hZSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (actualHartreePhasedScaledRadiation z ell time gamma s) x)
    (hVSecond : DifferentiableAt ℝ
      (deriv (fun y : ℝ => (V s y : ℂ))) r)
    (hZSecond : DifferentiableAt ℝ
      (deriv (actualHartreePhasedScaledRadiation z ell time gamma s)) r)
    (hFullRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ) +
          actualHartreePhasedScaledRadiation z ell time gamma s rho‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hCoreRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hRadiationRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖actualHartreePhasedScaledRadiation z ell time gamma s rho‖ ^ 4)
      (Ioi (0 : ℝ))) :
    actualOneLayerCommonPDEResidual V
      (actualHartreePhasedScaledRadiation z ell time gamma)
      (b s) (-gs) s r =
    actualOneLayerInteractionOnly V
      (actualHartreePhasedScaledRadiation z ell time gamma) s r := by
  let Z : ℝ → ℝ → ℂ :=
    actualHartreePhasedScaledRadiation z ell time gamma
  have hPDE :
      complexRadialRenormalizedResidual Z (b s) (-gs) s r = 0 := by
    exact actual_Hartree_phased_physical_flow_true_renormalized_PDE
      ell time b gamma z s r gs hell hr hEll hClock hGamma
      L zt zr hJoint hJac hzSpace hzSecond hzDeriv hPhysicalPDE
  exact actual_one_layer_PDE_radiation_evolution_cancelled
    V Z (b s) (-gs) s r hVTime hZTime hVSpace hZSpace
      hVSecond hZSecond hFullRow hCoreRow hRadiationRow hPDE

/-- The two actual H+/H- sources are precisely the real and
imaginary parts of the same nonlinear interaction, with no
postulated radiation-PDE cancellation. -/
theorem actual_Hartree_physical_flow_both_channels_are_interactions
    (V : ℝ → ℝ → ℝ)
    (ell time b gamma : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ) (s r gs : ℝ)
    (hell : 0 < ell s) (hr : 0 < r)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hClock : HasDerivAt time ((ell s) ^ 2) s)
    (hGamma : HasDerivAt gamma gs s)
    (L : (ℝ × ℝ) →L[ℝ] ℂ) (zt zr : ℂ)
    (hJoint : HasFDerivAt (fun p : ℝ × ℝ => z p.1 p.2) L
      (time s, ell s * r))
    (hJac : ∀ a c : ℝ,
      L (a,c) = (a : ℂ) * zt + (c : ℂ) * zr)
    (hzSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (z (time s)) (ell s * x))
    (hzSecond : DifferentiableAt ℝ (deriv (z (time s))) (ell s * r))
    (hzDeriv : deriv (z (time s)) (ell s * r) = zr)
    (hPhysicalPDE :
      Complex.I * zt +
        complexRadialLaplacian (z (time s)) (ell s * r) +
        complexRadialHartreeNonlinearity (z (time s)) (ell s * r) = 0)
    (hVTime : DifferentiableAt ℝ
      (fun t : ℝ => (V t r : ℂ)) s)
    (hZTime : DifferentiableAt ℝ
      (fun t : ℝ => actualHartreePhasedScaledRadiation z ell time gamma t r) s)
    (hVSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (fun y => (V s y : ℂ)) x)
    (hZSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (actualHartreePhasedScaledRadiation z ell time gamma s) x)
    (hVSecond : DifferentiableAt ℝ
      (deriv (fun y : ℝ => (V s y : ℂ))) r)
    (hZSecond : DifferentiableAt ℝ
      (deriv (actualHartreePhasedScaledRadiation z ell time gamma s)) r)
    (hFullRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ) +
          actualHartreePhasedScaledRadiation z ell time gamma s rho‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hCoreRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hRadiationRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖actualHartreePhasedScaledRadiation z ell time gamma s rho‖ ^ 4)
      (Ioi (0 : ℝ))) :
    actualOneLayerPlusPDE V
      (actualHartreePhasedScaledRadiation z ell time gamma)
      (b s) (-gs) s r =
      (actualOneLayerInteractionOnly V
        (actualHartreePhasedScaledRadiation z ell time gamma) s r).re ∧
    actualOneLayerMinusPDE V
      (actualHartreePhasedScaledRadiation z ell time gamma)
      (b s) (-gs) s r =
      (actualOneLayerInteractionOnly V
        (actualHartreePhasedScaledRadiation z ell time gamma) s r).im := by
  have h := actual_Hartree_physical_flow_forces_common_interaction_source
    V ell time b gamma z s r gs hell hr
    hEll hClock hGamma L zt zr hJoint hJac hzSpace hzSecond
    hzDeriv hPhysicalPDE hVTime hZTime hVSpace hZSpace
    hVSecond hZSecond hFullRow hCoreRow hRadiationRow
  exact ⟨congrArg Complex.re h, congrArg Complex.im h⟩

end HBL.TypeIIDynamicSelection
