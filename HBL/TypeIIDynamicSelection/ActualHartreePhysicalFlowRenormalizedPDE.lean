import HBL.TypeIIDynamicSelection.ActualHartreeCriticalRadialLaplacianScaling
import HBL.TypeIIDynamicSelection.ActualPhysicalHartreeScaleTimeJet
import HBL.TypeIIDynamicSelection.ActualHartreeCriticalNonlinearityScaling
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
  let Z : ℝ → ℝ → ℂ :=
    fun τ x => rescalePhysicalRadiation (ell τ) (z (time τ)) x
  have hTime :=
    actual_Hartree_physical_scale_clock_explicit_time_jet
      ell time b z s r L zt zr hEll hell hClock hJoint hJac
  have hLap :=
    actual_Hartree_critical_rescaled_radial_Laplacian
      (ell s) r hell hr (z (time s)) hzSpace hzSecond
  have hNL :=
    actual_Hartree_critical_scaled_nonlinearity
      (ell s) r hell (z (time s))
  have hDil :=
    actual_Hartree_critical_rescaled_dilation
      (ell s) r (z (time s)) (hzSpace r)
  have hsqrtpos : 0 < Real.sqrt (ell s) := Real.sqrt_pos.2 hell
  have hsqrtCoeff :
      (-(b s * ell s)) / (2 * Real.sqrt (ell s)) =
        -(b s * Real.sqrt (ell s)) / 2 := by
    have hsqrtNe : 2 * Real.sqrt (ell s) ≠ 0 := by positivity
    apply (div_eq_iff hsqrtNe).2
    calc
      -(b s * ell s) = -(b s * (Real.sqrt (ell s)) ^ 2) := by
        rw [Real.sq_sqrt hell.le]
      _ = (-(b s * Real.sqrt (ell s)) / 2) *
            (2 * Real.sqrt (ell s)) := by ring
  have hTimeEq :
      deriv (fun τ => Z τ r) s =
        (((-(b s * ell s)) /
            (2 * Real.sqrt (ell s)) : ℝ) : ℂ) *
              z (time s) (ell s * r) +
          (Real.sqrt (ell s) : ℂ) *
            (((ell s) ^ 2 : ℝ) * zt +
              ((-(b s * ell s)) * r : ℝ) * zr) := by
    simpa only [Z] using hTime.deriv
  change Complex.I * deriv (fun τ => Z τ r) s +
      complexRadialLaplacian (Z s) r +
      complexRadialHartreeNonlinearity (Z s) r +
      Complex.I * ((b s : ℝ) : ℂ) *
        complexRadialDilation (Z s) r +
      ((0 : ℝ) : ℂ) * Z s r = 0
  rw [hTimeEq, hLap, hNL, hDil]
  simp only [zero_mul, add_zero]
  rw [hsqrtCoeff]
  unfold complexRadialDilation
  rw [hzDeriv]
  push_cast
  calc
    _ = (((ell s) ^ 2 * Real.sqrt (ell s) : ℝ) : ℂ) *
        (Complex.I * zt +
          complexRadialLaplacian (z (time s)) (ell s * r) +
          complexRadialHartreeNonlinearity (z (time s)) (ell s * r)) := by
          push_cast
          ring
    _ = 0 := by rw [hPhysicalPDE]; ring

end HBL.TypeIIDynamicSelection
