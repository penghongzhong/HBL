import HBL.TypeIIDynamicSelection.ActualPhysicalHartreePDEToRenormalized
import HBL.TypeIIDynamicSelection.ActualHartreeDynamicPhaseCovariance
import Mathlib.Tactic

/-!
# One genuine physical Hartree flow -> fully PHASED renormalized PDE

This is the missing same-orbit analytical transport in original HBL 2.12.

The original physical flow z(t,r) is assumed to satisfy the pointwise
original inverse-square radial Hartree PDE at the sampled spacetime
point, with its genuine joint C1 time/space jet and radial C2 spatial
regularity. The concentration ell(s), physical clock t(s), and phase
gamma(s) are actual differentiable functions satisfying only

 ell_s = -b(s) ell(s),     t_s = ell(s)^2.

The complete complex field is derived from that same flow:

 Z_gamma(s,r) = exp(-i gamma(s)) sqrt(ell(s)) z(t(s),ell(s) r).

Previously established native Lean theorems prove exact full nonlinear
Hartree Riesz critical covariance, full 3D radial Laplacian scaling,
the real physical joint time/space chain rule, and complex dynamical
phase covariance. Their composition now DERIVES

  R(Z_gamma; b(s), -gamma_s)(s,r) = 0

without passing a renormalized radiation-PDE hypothesis. No terminal
support persistence, new source, selected Type-II exponent, axiom,
or artificial local Hartree cubic is introduced.

A separately cited high-regularity local-theory -> pointwise radial
Sobolev representative upgrade and the actual one-layer weight/gain
estimates are still needed for ORIGINAL 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole

/-- The real physical Hartree regular radiation with its actual
critical-scale/clock and dynamical phase, not a prescribed profile. -/
def actualPhysicalHartreePhasedFlow
    (ell time gamma : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (s r : ℝ) : ℂ :=
  actualHartreeUnitPhase (gamma s) *
    actualPhysicalHartreeRescaledFlow ell time z s r

/-- True physical Hartree PDE implies that its SAME dynamically phased
critical pullback solves the genuine original renormalized Hartree PDE,
with the phase velocity forced by the chain rule. -/
theorem actual_Hartree_same_physical_flow_forces_phased_renormalized_PDE
    (ell time b gamma : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ)
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
    (hZSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (z (time s)) (ell s * x))
    (hZSecond : DifferentiableAt ℝ
      (deriv (z (time s))) (ell s * r))
    (hPhysicalHartree :
      Complex.I * zt +
        complexRadialLaplacian (z (time s)) (ell s * r) +
        complexRadialHartreeNonlinearity (z (time s)) (ell s * r) = 0) :
    complexRadialRenormalizedResidual
      (actualPhysicalHartreePhasedFlow ell time gamma z)
      (b s) (-gs) s r = 0 := by
  let Z : ℝ → ℝ → ℂ :=
    actualPhysicalHartreeRescaledFlow ell time z
  have hPDE :
      complexRadialRenormalizedResidual Z (b s) 0 s r = 0 :=
    actual_Hartree_physical_flow_implies_renormalized_PDE
      ell time b z s r L zt zr
      hEll hEllPos hClock hJoint hJacobian hZR hr
      hZSpace hZSecond hPhysicalHartree
  have hTime : DifferentiableAt ℝ (fun t : ℝ => Z t r) s :=
    (actual_Hartree_physical_scale_clock_explicit_time_jet
      ell time b z s r L zt zr
      hEll hEllPos hClock hJoint hJacobian).differentiableAt
  have hSpace (x : ℝ) : DifferentiableAt ℝ (Z s) x := by
    have hscale : HasDerivAt (fun y : ℝ => ell s * y) (ell s) x :=
      hasDerivAt_const_mul (ell s)
    have h :=
      ((hZSpace x).hasDerivAt.scomp x hscale).const_mul
        (Real.sqrt (ell s) : ℂ)
    exact h.differentiableAt
  have hFirstEq :
      deriv (Z s) =
        fun x : ℝ => (Real.sqrt (ell s) : ℂ) *
          ((ell s : ℂ) * deriv (z (time s)) (ell s * x)) := by
    funext x
    exact actual_Hartree_critical_rescaled_radial_deriv
      (ell s) x (z (time s)) (hZSpace x)
  have hSecond : DifferentiableAt ℝ (deriv (Z s)) r := by
    rw [hFirstEq]
    have hscale : HasDerivAt (fun y : ℝ => ell s * y) (ell s) r :=
      hasDerivAt_const_mul (ell s)
    have h := hZSecond.hasDerivAt.scomp r hscale
    have hh := (h.const_mul (ell s : ℂ)).const_mul
      (Real.sqrt (ell s) : ℂ)
    exact hh.differentiableAt
  have hCov :=
    actual_Hartree_dynamic_phase_full_PDE_residual_covariant
      gamma Z (b s) 0 s r gs hGamma hTime hSpace hSecond
  change complexRadialRenormalizedResidual
      (fun t x => actualHartreeUnitPhase (gamma t) * Z t x)
      (b s) (-gs) s r = 0
  rw [show (0 : ℝ) - gs = -gs by ring] at hCov
  rw [hCov, hPDE, mul_zero]

end HBL.TypeIIDynamicSelection
