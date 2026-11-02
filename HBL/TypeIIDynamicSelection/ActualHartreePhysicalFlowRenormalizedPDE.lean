import HBL.TypeIIDynamicSelection.ActualHartreeCriticalRadialLaplacianScaling
import HBL.TypeIIDynamicSelection.ActualPhysicalHartreeScaleTimeJet
import HBL.TypeIIDynamicSelection.ActualHartreeCriticalNonlinearityScaling
import HBL.TypeIIDynamicSelection.ActualPhysicalHartreePDEToRenormalized
import Mathlib.Tactic

/-!
# Actual physical radial Hartree PDE -> renormalized radiation PDE

This is an indispensable NOT-YET-CLOSED step in manuscript original
2.12. The physical high-regularity Hartree local flow is connected to
the genuine radial renormalized Hartree radiation equation.

Let Z(s,r)=sqrt(ell(s))*z(time(s),ell(s)*r), with the original PDE
clock t_s=ell(s)^2, ell_s=-b(s)*ell(s). The ACTUAL
three-dimensional radial Laplacian, full inverse-square quartic Riesz
term, 1/2+r*d_r dilation, and two-variable physical time derivative
give the exact cancellation

  R_H(Z;b,omega=0)=ell^2 sqrt(ell) *
    (i z_t + Delta_rad z + (|.|^-2*|z|^4)|z|^2*z)=0.

The actual physical radial PDE, C1 spacetime representative, local
Sobolev pointwise identification, and second spatial derivative are
visible inputs. Crucially we no longer assume the CONCLUSION
R_H(Z)=0 as an independent literature-interface premise.

No new axiom, no assumed Type II rate or Kummer source gain. A phase
rotation with physically forced omega follows separately from the
already strict dynamic phase covariance.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- An actual physical radial Hartree strong solution, evaluated at
its proper physical clock/scale, solves the exact renormalized
inverse-square Hartree PDE with omega=0 at every positive radius. -/
theorem actual_Hartree_physical_flow_true_renormalized_PDE
    (ell time b : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ) (s r : ℝ)
    (hell : 0 < ell s) (hr : 0 < r)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hClock : HasDerivAt time ((ell s) ^ 2) s)
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
      (fun τ x => rescalePhysicalRadiation (ell τ) (z (time τ)) x)
      (b s) 0 s r = 0 := by
  have hPhysical :=
    actual_Hartree_physical_flow_implies_renormalized_PDE
      ell time b z s r L zt zr
      hEll hell hClock hJoint hJac hzDeriv.symm hr
      hzSpace hzSecond hPhysicalPDE
  simpa only [actualPhysicalHartreeRescaledFlow] using hPhysical

end HBL.TypeIIDynamicSelection
