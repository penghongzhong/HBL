import HBL.TypeIIDynamicSelection.ActualHartreePhysicalPDECoreSourceClosure
import HBL.TypeIIDynamicSelection.ActualOneLayerRadiationPDECancellation
import Mathlib.Tactic

/-!
# HBL original 2.12: BOTH H+/H- sources from the SAME physical Hartree flow

The earlier exact two-channel interaction cancellation
  Re/Im[R_H(V+Z)-R_H(V)] = Re/Im[HartreeFullInteraction(V,Z)]
accepted `R_H(Z)=0` as an input. Here that input is no longer
postulated. The SAME actual physical energy-critical 3D Hartree
solution z(t,r), its true t_s=ell^2 / ell_s=-b ell clock and the
physical phase gamma(s) imply it from the exact radial Laplacian,
full nonlocal quartic inverse-square Riesz scaling and 2D
spacetime Frechet chain rule.

The right-hand-side contains ALL three full physical nonlocal
Hartree cross interactions, not an abstract source or local
cubic replacement. The conditions about the physical flow's
pointwise H^L representative, Riesz-row integrability, and
the core profile V are explicit. They are to be instantiated
from published high-regularity Hartree theory and the actual
selected orbit. Full original 2.12 boundary/weight matching
remains a separate requirement.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Derive BOTH genuine Hartree Fredholm channel sources from the
REAL physical strong solution. The radiation PDE is NOT assumed
as an extra hypothesis: it follows from its physical PDE,
critical scaling and clock/phase. -/
theorem actual_one_layer_Hplus_Hminus_from_one_physical_Hartree_flow
    (ell time b gamma : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (V : ℝ → ℝ → ℝ) (s r gs : ℝ)
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
    (hPhysicalPDE : Complex.I * zt +
      complexRadialLaplacian (z (time s)) (ell s * r) +
      complexRadialHartreeNonlinearity (z (time s)) (ell s * r) = 0)
    (hVTime : DifferentiableAt ℝ (fun t : ℝ => (V t r : ℂ)) s)
    (hVSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (fun y : ℝ => (V s y : ℂ)) x)
    (hVSecond : DifferentiableAt ℝ
      (deriv (fun y : ℝ => (V s y : ℂ))) r)
    (hFullRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ) + actualHartreeUnitPhase (gamma s) *
          rescalePhysicalRadiation (ell s) (z (time s)) rho‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hCoreRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ)‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hRadiationRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖actualHartreeUnitPhase (gamma s) *
          rescalePhysicalRadiation (ell s) (z (time s)) rho‖ ^ 4)
      (Ioi (0 : ℝ))) :
    let Z : ℝ → ℝ → ℂ :=
      fun tau x => actualHartreeUnitPhase (gamma tau) *
        rescalePhysicalRadiation (ell tau) (z (time tau)) x
    actualOneLayerPlusPDE V Z (b s) (-gs) s r =
      (actualOneLayerInteractionOnly V Z s r).re ∧
    actualOneLayerMinusPDE V Z (b s) (-gs) s r =
      (actualOneLayerInteractionOnly V Z s r).im := by
  dsimp
  let Z : ℝ → ℝ → ℂ :=
    fun tau x => actualHartreeUnitPhase (gamma tau) *
      rescalePhysicalRadiation (ell tau) (z (time tau)) x
  have hUnphasedTime :=
    actual_Hartree_physical_scale_clock_explicit_time_jet
      ell time b z s r L zt zr hEll hell hClock hJoint hJac
  have hZTime : DifferentiableAt ℝ (fun tau : ℝ => Z tau r) s := by
    have hPhase := actual_Hartree_dynamic_unit_phase_hasDerivAt
      gamma s gs hGamma
    have hp := hPhase.mul hUnphasedTime
    exact hp.differentiableAt
  have hScaledSpace : ∀ x : ℝ,
      DifferentiableAt ℝ
        (rescalePhysicalRadiation (ell s) (z (time s))) x := by
    intro x
    have hscale : HasDerivAt (fun y : ℝ => ell s * y)
        (ell s) x := hasDerivAt_const_mul (ell s)
    exact (((hzSpace x).hasDerivAt.scomp x hscale).const_mul
      (Real.sqrt (ell s) : ℂ)).differentiableAt
  have hZSpace : ∀ x : ℝ, DifferentiableAt ℝ (Z s) x := by
    intro x
    exact ((hScaledSpace x).hasDerivAt.const_mul
      (actualHartreeUnitPhase (gamma s))).differentiableAt
  have hScaledFirst :
      deriv (rescalePhysicalRadiation (ell s) (z (time s))) =
        fun x => (Real.sqrt (ell s) : ℂ) *
          ((ell s : ℝ) : ℂ) * deriv (z (time s)) (ell s * x) := by
    funext x
    simpa only [mul_assoc] using
      actual_Hartree_critical_rescaled_radial_deriv
        (ell s) x (z (time s)) (hzSpace x)
  have hScaledSecond : DifferentiableAt ℝ
      (deriv (rescalePhysicalRadiation (ell s) (z (time s)))) r := by
    rw [hScaledFirst]
    have hscale : HasDerivAt (fun y : ℝ => ell s * y) (ell s) r :=
      hasDerivAt_const_mul (ell s)
    simpa only [Function.comp_def, mul_assoc] using
      (((hzSecond.hasDerivAt.scomp r hscale).const_mul
        ((ell s : ℝ) : ℂ)).const_mul
          (Real.sqrt (ell s) : ℂ)).differentiableAt
  have hZSecond : DifferentiableAt ℝ (deriv (Z s)) r := by
    let hPhase : ℂ := actualHartreeUnitPhase (gamma s)
    have hDerivEq :
        deriv (Z s) = fun x =>
          hPhase * deriv
            (rescalePhysicalRadiation (ell s) (z (time s))) x := by
      funext x
      change
        deriv (fun y => hPhase *
          rescalePhysicalRadiation (ell s) (z (time s)) y) x =
          hPhase * deriv
            (rescalePhysicalRadiation (ell s) (z (time s))) x
      exact ((hScaledSpace x).hasDerivAt.const_mul hPhase).deriv
    rw [hDerivEq]
    exact (hScaledSecond.hasDerivAt.const_mul hPhase).differentiableAt
  have hCommon :=
    actual_Hartree_physical_flow_forces_one_layer_interaction_only
      V ell time b gamma z s r gs L zt zr
      hEll hell hClock hGamma hJoint hJac hzDeriv.symm
      hr hzSpace hzSecond hPhysicalPDE
      hVTime hZTime hVSpace hZSpace hVSecond hZSecond
      hFullRow hCoreRow hRadiationRow
  exact ⟨congrArg Complex.re hCommon,
    congrArg Complex.im hCommon⟩

end HBL.TypeIIDynamicSelection
