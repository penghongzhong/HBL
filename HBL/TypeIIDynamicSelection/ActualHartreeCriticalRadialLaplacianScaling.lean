import HBL.TypeIIDynamicSelection.ActualHartreeRadialDilationScaling
import Mathlib.Tactic

/-!
# Genuine 3D radial Laplacian covariance of the physical Hartree radiation

This fills the SECOND spatial-derivative leg of the real physical
Hartree flow -> renormalized Hartree PDE bridge in original 2.12.

For f_ell(r) = sqrt(ell)*z(ell*r), with 0<ell and r>0,
  Delta_rad f_ell(r) = ell^2 sqrt(ell) Delta_rad z(ell*r).
Crucially this uses the full 3D Delta_rad = d_rr + (2/r)d_r,
not a 1D Laplacian or an abstract imposed source.

Time/phase derivatives and the actual high-regularity physical PDE
remain explicit inputs for the subsequent full-radiation cancellation.
No new axiom or Type II rate is introduced.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Exact physical 3D radial Laplacian of a genuine critical Hartree
radiation, including the 2/r first derivative. -/
theorem actual_Hartree_critical_rescaled_radial_Laplacian
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (z : ℝ → ℂ)
    (hzSpace : ∀ x : ℝ, DifferentiableAt ℝ z (ell * x))
    (hzSecond : DifferentiableAt ℝ (deriv z) (ell * r)) :
    complexRadialLaplacian (rescalePhysicalRadiation ell z) r =
      ((ell ^ 2 * Real.sqrt ell : ℝ) : ℂ) *
        complexRadialLaplacian z (ell * r) := by
  have hFirstEq :
      deriv (rescalePhysicalRadiation ell z) =
        fun x => (Real.sqrt ell : ℂ) *
          ((ell : ℂ) * deriv z (ell * x)) := by
    funext x
    exact actual_Hartree_critical_rescaled_radial_deriv
      ell x z (hzSpace x)
  have hScale : HasDerivAt (fun y : ℝ => ell * y) ell r :=
    hasDerivAt_const_mul ell
  have hInner : HasDerivAt
      (fun y : ℝ => deriv z (ell * y))
      ((ell : ℂ) * deriv (deriv z) (ell * r)) r :=
    hzSecond.hasDerivAt.scomp r hScale
  have hSecondEq :
      deriv (deriv (rescalePhysicalRadiation ell z)) r =
        (Real.sqrt ell : ℂ) *
          ((ell : ℂ) * ((ell : ℂ) * deriv (deriv z) (ell * r))) := by
    rw [hFirstEq]
    have hs := ((hInner.const_mul (ell : ℂ)).const_mul
      (Real.sqrt ell : ℂ)).deriv
    simpa only [mul_assoc] using hs
  have hEllC : (ell : ℂ) ≠ 0 := by
    exact_mod_cast hell.ne'
  have hrC : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hScaleC : ((ell * r : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos hell hr).ne'
  unfold complexRadialLaplacian
  rw [hSecondEq,
    actual_Hartree_critical_rescaled_radial_deriv
      ell r z (hzSpace r)]
  push_cast
  field_simp [hEllC, hrC, hScaleC]

end HBL.TypeIIDynamicSelection
