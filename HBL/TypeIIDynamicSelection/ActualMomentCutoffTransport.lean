import HBL.TypeIIDynamicSelection.ActualRadiationMomentDynamics
import HBL.TypeIIDynamicSelection.ActualOneLayerPDEResidual
import Mathlib.Tactic

/-!
# Exact physical radiation-moment cancellation in the moving radial cutoff

The actual exterior Hartree monopole coefficient c(s) is the rescaled
three-dimensional quartic radiation moment, not a prescribed rate.
For the physical smooth inner cutoff eta_c(s,r)=1-chi(c(s)*r/4),
the transport derivative (\partial_s + b(s) r \partial_r) eta_c
has NO bare b(s)c(s) term: the genuine radiation moment derivative
is the only surviving source.

When c(s)>0, this is exactly the manuscript cutoff
1-chi(r/R(s)) with R(s)=4/|c(s)|. No chosen terminal blowup exponent,
extra axiom or derived source-size estimate is asserted.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology ContDiff

namespace HBL.TypeIIDynamicSelection

open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual smooth moving cutoff, expressed through the physical
whole-radiation centre moment, avoiding division by a possibly zero c. -/
def actualMomentInnerCutoff
    (ell : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    (s r : ℝ) : ℝ :=
  1 - cutoff (actualPhysicalRadiationMonopole ell z time s * r / 4)

/-- Exact radial derivative of the true radiation-moment cutoff. -/
theorem actualMomentInnerCutoff_space_hasDerivAt
    (ell : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    (s r : ℝ) :
    HasDerivAt (actualMomentInnerCutoff ell z time s)
      (-deriv cutoff
        (actualPhysicalRadiationMonopole ell z time s * r / 4) *
        (actualPhysicalRadiationMonopole ell z time s / 4)) r := by
  let c := actualPhysicalRadiationMonopole ell z time s
  have harg : HasDerivAt (fun x : ℝ => c * x / 4) (c / 4) r := by
    convert ((hasDerivAt_id r).const_mul c).div_const 4 using 1
    · funext x
      rfl
    · ring
  have hcut : HasDerivAt cutoff
      (deriv cutoff (c * r / 4)) (c * r / 4) :=
    ((contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).1
      (c * r / 4)).hasDerivAt
  have hval := (hasDerivAt_const r (1 : ℝ)).sub (hcut.comp r harg)
  convert hval using 1
  · rfl
  · ring

/-- The actual time derivative of the same cutoff follows from the
physical Hartree radiation-moment flow. The moment time derivative
is an explicit high-regularity input (not a prescribed parameter). -/
theorem actualMomentInnerCutoff_time_hasDerivAt
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    {s dm : ℝ} (r : ℝ)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hMoment : HasDerivAt
      (fun t => radialPhysicalQuarticMoment (z t)) dm (time s)) :
    HasDerivAt (fun t => actualMomentInnerCutoff ell z time t r)
      (-deriv cutoff
         (actualPhysicalRadiationMonopole ell z time s * r / 4) *
        ((-(b s * actualPhysicalRadiationMonopole ell z time s) +
          hartreeKappa * (ell s) ^ 3 * dm) * r / 4)) s := by
  let c := actualPhysicalRadiationMonopole ell z time
  have hc := actual_physical_radiation_slow_coefficient_hasDerivAt
    ell b z time hEll hEllPos hTime hMoment
  have harg : HasDerivAt (fun t => c t * r / 4)
      ((-(b s * c s) + hartreeKappa * (ell s) ^ 3 * dm) * r / 4) s := by
    convert (hc.mul_const r).div_const 4 using 1
  have hcut : HasDerivAt cutoff
      (deriv cutoff (c s * r / 4)) (c s * r / 4) :=
    ((contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).1
      (c s * r / 4)).hasDerivAt
  have ht := (hasDerivAt_const s (1 : ℝ)).sub (hcut.comp s harg)
  convert ht using 1
  · rfl
  · ring

/-- ACTUAL core-to-annulus transport cancellation: the bare b*c
from the moving cutoff is exactly absorbed by its radial dilation.
Only the physical quartic radiation-moment derivative remains. -/
theorem actualMomentInnerCutoff_material_derivative
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    {s dm : ℝ} (r : ℝ)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hMoment : HasDerivAt
      (fun t => radialPhysicalQuarticMoment (z t)) dm (time s)) :
    deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
      b s * r * deriv (actualMomentInnerCutoff ell z time s) r =
    -(hartreeKappa * (ell s) ^ 3 * dm * r / 4) *
      deriv cutoff
        (actualPhysicalRadiationMonopole ell z time s * r / 4) := by
  have ht := (actualMomentInnerCutoff_time_hasDerivAt
    ell b z time r hEll hEllPos hTime hMoment).deriv
  have hx := (actualMomentInnerCutoff_space_hasDerivAt
    ell z time s r).deriv
  rw [ht, hx]
  ring

end HBL.TypeIIDynamicSelection
