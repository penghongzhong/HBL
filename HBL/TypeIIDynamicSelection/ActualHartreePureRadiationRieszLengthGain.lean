import HBL.TypeIIDynamicSelection.ActualHartreeRadialPDECriticalScaling
import HBL.TypeIIDynamicSelection.ActualHartreeStraussRieszEnvelope
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# True Hartree full pure-radiation Riesz potential gains one physical length power

The true 3D inverse-square Hartree radiation Z_ell(r)=sqrt(ell)*z(ell*r)
satisfies the already proved EXACT radial logarithmic-kernel covariance:
 P[|Z_ell|^4](r)=ell*P[|z|^4](ell*r).

The existing physical radial Strauss/H1 plus L-infinity estimate
 |z(rho)|^4 <=2(B^4+A^4)*bubble(rho)^2
and proved absolute Hartree row bound immediately give
 |P[|Z_ell|^4](r)| <= ell*C_row*2(B^4+A^4),
for every 0<r, every ell>0 and one genuine regular radiation slice.
No artificial local cubic, prescribed blowup rate or new axiom.

This is a real nonlinear source component, but by itself it does
not establish the full weighted L2 local-cubic difference or 2.13.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The entire genuine pure-radiation Hartree quartic Riesz potential
has an explicit O(ell) positive critical-scaling gain.
Its constant comes from the already strictly verified real inverse-square
Hartree kernel and radial H1/Strauss controls; no time-rate input. -/
theorem actual_Hartree_pure_radiation_Riesz_uniform_length_gain
    (ell r B A : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    |radialHartreePotential
      (fun rho => ‖rescalePhysicalRadiation ell z rho‖ ^ 4) r| ≤
        (radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4))) * ell := by
  have hM : 0 ≤ 2 * (B ^ 4 + A ^ 4) := by positivity
  have hDensity (rho : ℝ) (hrho : 0 < rho) :
      |‖z rho‖ ^ 4| ≤ (2 * (B ^ 4 + A ^ 4)) * bubble rho ^ 2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ ‖z rho‖ ^ 4)]
    exact actual_Hartree_radial_quartic_envelope_from_Strauss
      z B A hB hA hSup hStrauss rho hrho
  have hOld : |radialHartreePotential
      (fun rho => ‖z rho‖ ^ 4) (ell * r)| ≤
        radialHartreeRowBoundConstant * (2 * (B ^ 4 + A ^ 4)) :=
    (radialHartreePotential_bubble_sq_domination
      (fun rho => ‖z rho‖ ^ 4) (hz.norm.pow_const 4)
      hM hDensity (mul_pos hell hr)).2
  rw [actual_Hartree_critical_radiation_Riesz_scaling ell r hell z]
  rw [abs_mul, abs_of_pos hell]
  calc
    ell * |radialHartreePotential
      (fun rho => ‖z rho‖ ^ 4) (ell * r)| ≤
        ell * (radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4))) :=
      mul_le_mul_of_nonneg_left hOld hell.le
    _ = (radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4))) * ell := by ring

end HBL.TypeIIDynamicSelection
