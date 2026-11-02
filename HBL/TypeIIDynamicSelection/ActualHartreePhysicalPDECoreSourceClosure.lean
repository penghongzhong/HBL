import HBL.TypeIIDynamicSelection.ActualPhysicalHartreePhasedPDEElimination
import HBL.TypeIIDynamicSelection.ActualOneLayerRadiationPDECancellation
import Mathlib.Tactic

/-!
# HBL original 2.12: Hartree source cancellation from the PHYSICAL PDE

Earlier same-PDE two-channel source decomposition required the extra
hypothesis that the offterminal renormalized radiation solves
  R(Z;b,omega)=0.
That is not a suitable independent input for the original theorem.

Here Z is explicitly the SAME physical high-regularity radiation
z(t,r), transported through the true dynamical concentration scale,
physical clock and complex gauge:

 Z(s,r)=exp(-i gamma(s))*sqrt(ell(s))*z(time(s),ell(s)r).

The actual physical Hartree equation, joint C1 spacetime jet,
radial C2 regularity, and real modulation equations
  ell_s=-b ell, time_s=ell^2
DERIVE the needed renormalized radiation PDE. The previously
verified complete inverse-square Hartree nonlinear cancellation
then proves the ONLY remaining core-bubble interaction is

 R(V+Z)-R(V) = N(V+Z)-N(V)-N(Z),

retaining all real/imaginary and mixed radial Riesz interactions.
NO renormalized radiation-PDE or fixed Type II rate is among the
hypotheses. The high-regularity pointwise physical radial lift and
the three actual Hartree potential-integral rows are visible.

This is still a source-level core lemma: weighted source norm,
inner--Kummer--remote jet gluing and the full weight-gain ledger
must be established before original 2.12 is accepted.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The full physical Hartree PDE, not a postulated renormalized
radiation equation, forces all pure radiation terms to cancel in
the original ONE residual shared by both H+ and H- channels. -/
theorem actual_Hartree_physical_flow_forces_one_layer_interaction_only
    (V : ℝ → ℝ → ℝ)
    (ell time b gamma : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (s r gs : ℝ) (L : ℝ × ℝ →L[ℝ] ℂ) (zt zr : ℂ)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hClock : HasDerivAt time ((ell s) ^ 2) s)
    (hGamma : HasDerivAt gamma gs s)
    (hJoint : HasFDerivAt
      (fun p : ℝ × ℝ => z p.1 p.2) L
      (time s, ell s * r))
    (hJacobian : ∀ a c : ℝ,
      L (a,c) = (a : ℂ) * zt + (c : ℂ) * zr)
    (hZR : zr = deriv (z (time s)) (ell s * r))
    (hr : 0 < r)
    (hZPhysicalSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (z (time s)) (ell s * x))
    (hZPhysicalSecond : DifferentiableAt ℝ
      (deriv (z (time s))) (ell s * r))
    (hPhysicalHartree :
      Complex.I * zt +
        complexRadialLaplacian (z (time s)) (ell s * r) +
        complexRadialHartreeNonlinearity (z (time s)) (ell s * r) = 0)
    (hVTime : DifferentiableAt ℝ (fun t : ℝ => (V t r : ℂ)) s)
    (hRadiationTime : DifferentiableAt ℝ
      (fun t => actualPhysicalHartreePhasedFlow ell time gamma z t r) s)
    (hVSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (fun y : ℝ => (V s y : ℂ)) x)
    (hRadiationSpace : ∀ x : ℝ,
      DifferentiableAt ℝ
        (actualPhysicalHartreePhasedFlow ell time gamma z s) x)
    (hVSecond : DifferentiableAt ℝ
      (deriv (fun y : ℝ => (V s y : ℂ))) r)
    (hRadiationSecond : DifferentiableAt ℝ
      (deriv (actualPhysicalHartreePhasedFlow ell time gamma z s)) r)
    (hFullRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ) +
          actualPhysicalHartreePhasedFlow ell time gamma z s rho‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hCoreRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ)‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hRadiationRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖actualPhysicalHartreePhasedFlow ell time gamma z s rho‖ ^ 4)
      (Ioi (0 : ℝ))) :
    actualOneLayerCommonPDEResidual V
        (actualPhysicalHartreePhasedFlow ell time gamma z)
        (b s) (-gs) s r =
      actualOneLayerInteractionOnly V
        (actualPhysicalHartreePhasedFlow ell time gamma z) s r := by
  have hRadiationPDE :
      complexRadialRenormalizedResidual
        (actualPhysicalHartreePhasedFlow ell time gamma z)
        (b s) (-gs) s r = 0 :=
    actual_Hartree_same_physical_flow_forces_phased_renormalized_PDE
      ell time b gamma z s r gs L zt zr
      hEll hEllPos hClock hGamma hJoint hJacobian
      hZR hr hZPhysicalSpace hZPhysicalSecond hPhysicalHartree
  exact actual_one_layer_PDE_radiation_evolution_cancelled
    V (actualPhysicalHartreePhasedFlow ell time gamma z)
    (b s) (-gs) s r
    hVTime hRadiationTime hVSpace hRadiationSpace
    hVSecond hRadiationSecond hFullRow hCoreRow
    hRadiationRow hRadiationPDE

end HBL.TypeIIDynamicSelection
