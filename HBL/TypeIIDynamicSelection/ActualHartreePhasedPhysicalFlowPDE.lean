import HBL.TypeIIDynamicSelection.ActualHartreePhysicalFlowRenormalizedPDE
import HBL.TypeIIDynamicSelection.ActualHartreeDynamicPhaseCovariance
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
  let Z : ℝ → ℝ → ℂ :=
    fun τ x => rescalePhysicalRadiation (ell τ) (z (time τ)) x
  have hUnphased :=
    actual_Hartree_physical_flow_true_renormalized_PDE
      ell time b z s r hell hr hEll hClock
      L zt zr hJoint hJac hzSpace hzSecond hzDeriv hPhysicalPDE
  have hTime :=
    actual_Hartree_physical_scale_clock_explicit_time_jet
      ell time b z s r L zt zr hEll hell hClock hJoint hJac
  have hZTime : DifferentiableAt ℝ (fun τ : ℝ => Z τ r) s := by
    exact hTime.differentiableAt
  have hZSpace : ∀ x : ℝ, DifferentiableAt ℝ (Z s) x := by
    intro x
    have hscale : HasDerivAt (fun y : ℝ => ell s * y) (ell s) x :=
      hasDerivAt_const_mul (ell s)
    have hfield := ((hzSpace x).hasDerivAt.scomp x hscale).const_mul
      (Real.sqrt (ell s) : ℂ)
    exact hfield.differentiableAt
  have hZFirstEq :
      deriv (Z s) =
        fun x => (Real.sqrt (ell s) : ℂ) *
          ((ell s : ℝ) : ℂ) *
            deriv (z (time s)) (ell s * x) := by
    funext x
    dsimp [Z]
    simpa only [mul_assoc] using
      (actual_Hartree_critical_rescaled_radial_deriv
        (ell s) x (z (time s)) (hzSpace x))
  have hZSecond : DifferentiableAt ℝ (deriv (Z s)) r := by
    rw [hZFirstEq]
    have hscale : HasDerivAt (fun y : ℝ => ell s * y) (ell s) r :=
      hasDerivAt_const_mul (ell s)
    simpa only [mul_assoc] using
      (((hzSecond.hasDerivAt.scomp r hscale).const_mul
        ((ell s : ℝ) : ℂ)).const_mul
          (Real.sqrt (ell s) : ℂ)).differentiableAt
  have hCov := actual_Hartree_dynamic_phase_full_PDE_residual_covariant
    gamma Z (b s) 0 s r gs hGamma hZTime hZSpace hZSecond
  calc
    complexRadialRenormalizedResidual
        (fun τ x => actualHartreeUnitPhase (gamma τ) *
          rescalePhysicalRadiation (ell τ) (z (time τ)) x)
        (b s) (-gs) s r =
      actualHartreeUnitPhase (gamma s) *
        complexRadialRenormalizedResidual Z (b s) 0 s r := by
          simpa only [Z, zero_sub] using hCov
    _ = 0 := by
      have hz : complexRadialRenormalizedResidual Z (b s) 0 s r = 0 :=
        hUnphased
      rw [hz]
      ring

end HBL.TypeIIDynamicSelection
