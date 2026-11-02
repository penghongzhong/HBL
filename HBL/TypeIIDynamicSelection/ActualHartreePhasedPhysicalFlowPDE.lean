import HBL.TypeIIDynamicSelection.ActualHartreePhysicalFlowRenormalizedPDE
import HBL.TypeIIDynamicSelection.ActualHartreeDynamicPhaseCovariance
import HBL.TypeIIDynamicSelection.ActualPhysicalHartreePhasedPDEElimination
import Mathlib.Tactic

/-!
# Original HBL 2.12: phase-selected physical flow solves the actual radiation PDE

Apply the TRUE nonlocal Hartree dynamic phase covariance to the true
physical regular flow's already established clock/critical scale
residual identity. In the manuscript's convention the physical phase
gamma(s) forces omega = -gamma_s; it is not an assigned source speed.

For Z(s,r)=sqrt(ell(s))*z(t(s),ell(s)r):
  R_H(exp(-i gamma) Z; b, -gamma_s) =
    exp(-i gamma) R_H(Z;b,0) = 0.

This eliminates the separate hypothesis `R_H(Z)=0` appearing in
the original 2.12 three-region PDE cancellation, for a radial
pointwise strong Hartree flow satisfying explicit physical analytic
input. Global Kummer/remote matching and positive-order full mixed
residual remain independent obligations, not literature axioms.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- A genuinely phase-corrected 3D Hartree physical strong solution
has zero full renormalized inverse-square PDE residual. -/
theorem actual_Hartree_phased_physical_flow_true_renormalized_PDE
    (ell time b gamma : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ) (s r gs : ℝ)
    (hell : 0 < ell s) (hr : 0 < r)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hClock : HasDerivAt time ((ell s) ^ 2) s)
    (hGamma : HasDerivAt gamma gs s)
    (L : (ℝ × ℝ) →L[ℝ] ℂ)
    (zt zr : ℂ)
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
        complexRadialHartreeNonlinearity (z (time s)) (ell s * r) = 0) :
    complexRadialRenormalizedResidual
      (fun τ x => actualHartreeUnitPhase (gamma τ) *
        rescalePhysicalRadiation (ell τ) (z (time τ)) x)
      (b s) (-gs) s r = 0 := by
  have hPhysical :=
    actual_Hartree_same_physical_flow_forces_phased_renormalized_PDE
      ell time b gamma z s r gs L zt zr
      hEll hell hClock hGamma hJoint hJac hzDeriv.symm
      hr hzSpace hzSecond hPhysicalPDE
  simpa only [actualPhysicalHartreePhasedFlow,
    actualPhysicalHartreeRescaledFlow] using hPhysical

end HBL.TypeIIDynamicSelection
