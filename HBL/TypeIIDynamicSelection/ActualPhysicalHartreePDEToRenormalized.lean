import HBL.TypeIIDynamicSelection.ActualPhysicalHartreeScaleTimeJet
import HBL.TypeIIDynamicSelection.ActualHartreeRadialLaplacianScaling
import HBL.TypeIIDynamicSelection.ActualHartreeCriticalNonlinearityScaling
import Mathlib.Tactic

/-!
# TRUE physical Hartree PDE -> exact renormalized radiation equation

For one genuine complex radial physical Hartree field z(t,r),
construct the EXACT energy-critical moving field

  Z(s,r) = sqrt(ell(s)) z(time(s),ell(s)r).

The scale and physical clock satisfy their actual differential identities
ell_s=-b(s)ell(s), time_s=ell(s)^2; no asymptotic Type-II rate
is inserted into the assumptions.

The same spatial C2 radial field and joint spacetime C1 physical
jet give the chain-rule identities. The original inverse-square
Riesz potential and FULL quintic Hartree nonlinearity have already
been shown to scale exactly as ell^(5/2). Therefore

  R(Z; b, 0)(s,r)
    = ell(s)^(5/2) [i z_t + Delta_rad z + N(z)](time(s),ell(s)r).

Thus the physical Hartree PDE forces R(Z;b,0)=0. This is the
actual analytical interface previously exposed as hRadiationPDE
in the one-layer source cancellation theorem. Its specialization
from the original Sobolev/distributional local flow to a pointwise
radial representative remains an explicit standard analytic
Sobolev-lift obligation, NOT claimed proved here.

There is no abstract inverse, prescribed physical blowup rate, axiom
or assumed renormalized PDE in either theorem.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole

/-- Full original physical Hartree radiation field under the actual
critical concentration scale and finite physical time clock. -/
def actualPhysicalHartreeRescaledFlow
    (ell time : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (s r : ℝ) : ℂ :=
  rescalePhysicalRadiation (ell s) (z (time s)) r

/-- Exact cancellation of the critical scale derivative against the
full original dilation generator Lambda=1/2+r d_r. -/
theorem actual_Hartree_physical_time_plus_dilation_exact
    (ell time b : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (s r : ℝ) (L : ℝ × ℝ →L[ℝ] ℂ)
    (zt zr : ℂ)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hClock : HasDerivAt time ((ell s)^2) s)
    (hJoint : HasFDerivAt
      (fun p : ℝ × ℝ => z p.1 p.2) L
      (time s, ell s * r))
    (hJacobian : ∀ a c : ℝ,
      L (a,c) = (a : ℂ) * zt + (c : ℂ) * zr)
    (hZR : zr = deriv (z (time s)) (ell s * r))
    (hZSpace : DifferentiableAt ℝ (z (time s)) (ell s * r)) :
    Complex.I * deriv
      (fun τ => actualPhysicalHartreeRescaledFlow ell time z τ r) s +
    Complex.I * (b s : ℂ) *
      complexRadialDilation
        (actualPhysicalHartreeRescaledFlow ell time z s) r =
    (((ell s)^2 * Real.sqrt (ell s) : ℝ) : ℂ) *
      (Complex.I * zt) := by
  have hTime :=
    (actual_Hartree_physical_scale_clock_explicit_time_jet
      ell time b z s r L zt zr
      hEll hEllPos hClock hJoint hJacobian).deriv
  have hDilation :=
    actual_Hartree_critical_rescaled_dilation
      (ell s) r (z (time s)) hZSpace
  have hSqrt : Real.sqrt (ell s) ≠ 0 :=
    (Real.sqrt_pos.2 hEllPos).ne'
  have hScaleDiv :
      -(b s * ell s) / (2 * Real.sqrt (ell s)) =
        -(b s * Real.sqrt (ell s)) / 2 := by
    calc
      _ = -(b s * (Real.sqrt (ell s))^2) /
            (2 * Real.sqrt (ell s)) := by
        rw [Real.sq_sqrt hEllPos.le]
      _ = -(b s * Real.sqrt (ell s)) / 2 := by
        field_simp [hSqrt]
  change
    Complex.I * deriv (fun τ =>
       rescalePhysicalRadiation (ell τ) (z (time τ)) r) s +
      Complex.I * (b s : ℂ) *
        complexRadialDilation
          (rescalePhysicalRadiation (ell s) (z (time s))) r = _
  rw [hTime, hDilation, hZR, hScaleDiv]
  unfold complexRadialDilation
  push_cast
  ring

/-- A REAL physical Hartree PDE pointwise, together with its genuine
positive-radius radial lift and dynamic critical scale/clock,
IMPLIES the original renormalized Hartree radiation equation.
No renormalized PDE is among the hypotheses. -/
theorem actual_Hartree_physical_flow_implies_renormalized_PDE
    (ell time b : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (s r : ℝ) (L : ℝ × ℝ →L[ℝ] ℂ)
    (zt zr : ℂ)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hClock : HasDerivAt time ((ell s)^2) s)
    (hJoint : HasFDerivAt
      (fun p : ℝ × ℝ => z p.1 p.2) L
      (time s, ell s * r))
    (hJacobian : ∀ a c : ℝ,
      L (a,c) = (a : ℂ) * zt + (c : ℂ) * zr)
    (hZR : zr = deriv (z (time s)) (ell s * r))
    (hr : 0 < r)
    (hZSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (z (time s)) (ell s * x))
    (hZSecond : DifferentiableAt ℝ
      (deriv (z (time s))) (ell s * r))
    (hPhysicalHartree :
      Complex.I * zt +
        complexRadialLaplacian (z (time s)) (ell s * r) +
        complexRadialHartreeNonlinearity (z (time s)) (ell s * r) = 0) :
    complexRadialRenormalizedResidual
      (actualPhysicalHartreeRescaledFlow ell time z) (b s) 0 s r = 0 := by
  have hTD := actual_Hartree_physical_time_plus_dilation_exact
      ell time b z s r L zt zr
      hEll hEllPos hClock hJoint hJacobian hZR (hZSpace r)
  have hL := actual_Hartree_critical_rescaled_radial_Laplacian
      (ell s) r hEllPos hr (z (time s)) hZSpace hZSecond
  have hNL := actual_Hartree_critical_scaled_nonlinearity
      (ell s) r hEllPos (z (time s))
  have hres :
      complexRadialRenormalizedResidual
        (actualPhysicalHartreeRescaledFlow ell time z) (b s) 0 s r =
      (Complex.I * deriv
        (fun τ => actualPhysicalHartreeRescaledFlow ell time z τ r) s +
        Complex.I * (b s : ℂ) *
          complexRadialDilation
            (actualPhysicalHartreeRescaledFlow ell time z s) r) +
        complexRadialLaplacian
          (actualPhysicalHartreeRescaledFlow ell time z s) r +
        complexRadialHartreeNonlinearity
          (actualPhysicalHartreeRescaledFlow ell time z s) r := by
    unfold complexRadialRenormalizedResidual
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    ring
  rw [hres, hTD]
  change
    (((ell s)^2 * Real.sqrt (ell s) : ℝ) : ℂ) *
        (Complex.I * zt) +
      complexRadialLaplacian
        (rescalePhysicalRadiation (ell s) (z (time s))) r +
      complexRadialHartreeNonlinearity
        (rescalePhysicalRadiation (ell s) (z (time s))) r = 0
  rw [hL, hNL]
  calc
    _ = (((ell s)^2 * Real.sqrt (ell s) : ℝ) : ℂ) *
        (Complex.I * zt +
          complexRadialLaplacian (z (time s)) (ell s * r) +
          complexRadialHartreeNonlinearity (z (time s)) (ell s * r)) := by
      ring
    _ = 0 := by rw [hPhysicalHartree]; ring

end HBL.TypeIIDynamicSelection
