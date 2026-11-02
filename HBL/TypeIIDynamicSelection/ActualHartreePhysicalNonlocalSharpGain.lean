import HBL.TypeIIDynamicSelection.ActualHartreePhysicalNonlocalCutoffGain
import HBL.TypeIIDynamicSelection.ActualHartreeCriticalNonlinearityScaling
import Mathlib.Tactic

/-!
# The genuine nonlocal Hartree commutator keeps its critical half-power

This is a derived statement about the TRUE physical inverse-square
Riesz quartic convolution, not an artificial local polynomial.
It sharpens the already proved physical-profile cutoff estimate by
applying it at unit spatial scale and using the EXACT established
energy-critical nonlocal covariance.

For f_ell(r) = sqrt(ell)*z(ell*r), the full cutoff commutator has
O(ell^2 sqrt(ell)), i.e., 5/2 spatial powers. The radial Riesz
envelope of the same physical datum is retained as an explicit
analytic hypothesis, not a postulated gain or presumed blowup rate.

The original 2.12 weighted three-region residual and dynamically
selected profile are not thereby completed.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

/-- Actual moving Hartree cutoff intertwines with critical scaling.
The physical radius is ell*R, not an independent approximate scale. -/
theorem actual_Hartree_overlap_cutoff_physical_scale
    (ell R r : ℝ) (hell : 0 < ell) (hR : 0 < R) :
    actualOneLayerInnerOverlapCutoff (ell * R) (ell * r) =
      actualOneLayerInnerOverlapCutoff R r := by
  have hratio : (ell * r) / (ell * R) = r / R := by
    field_simp [hell.ne', hR.ne']
  change ((1 - cutoff ((ell * r) / (ell * R)) : ℝ) : ℂ) =
      ((1 - cutoff (r / R) : ℝ) : ℂ)
  rw [hratio]

/-- FULL nonlocal inverse-square Hartree cutoff commutator of the
genuine critically rescaled radiation is O(ell^(5/2)).
No local cubic replacement and no prescribed rate enter this theorem. -/
theorem actual_Hartree_physical_nonlocal_cutoff_sharp_length_gain
    (ell R r B D : ℝ)
    (hell : 0 < ell) (hR : 0 < R) (hr : 0 < r)
    (hD : 0 ≤ D) (hB : 0 ≤ B)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hzAmp : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hzQuartic : ∀ u : ℝ, 0 < u →
      ‖z u‖ ^ 4 ≤ D * bubble u ^ 2) :
    ‖complexRadialHartreeNonlinearity
        (fun x => actualOneLayerInnerOverlapCutoff R x *
          rescalePhysicalRadiation ell z x) r -
      actualOneLayerInnerOverlapCutoff R r *
        complexRadialHartreeNonlinearity
          (rescalePhysicalRadiation ell z) r‖ ≤
      (2 * radialHartreeRowBoundConstant * D * B ^ 3) *
        ell ^ 2 * Real.sqrt ell := by
  let g : ℝ → ℂ :=
    fun u => actualOneLayerInnerOverlapCutoff (ell * R) u * z u
  have hUnitRescale : rescalePhysicalRadiation 1 z = z := by
    funext u
    simp [rescalePhysicalRadiation]
  have hAtOne :
      ‖complexRadialHartreeNonlinearity g (ell * r) -
        actualOneLayerInnerOverlapCutoff (ell * R) (ell * r) *
          complexRadialHartreeNonlinearity z (ell * r)‖ ≤
        2 * radialHartreeRowBoundConstant * D * B ^ 3 := by
    have hRaw :=
      actual_Hartree_physical_nonlocal_cutoff_commutator_length_squared
        1 (ell * R) (ell * r) B D
        (by norm_num) (by norm_num) (mul_pos hell hr)
        hD hB z hz hzAmp hzQuartic
    rw [hUnitRescale] at hRaw
    simpa only [g, one_pow, mul_one] using hRaw
  have hScaledField :
      (fun x => actualOneLayerInnerOverlapCutoff R x *
        rescalePhysicalRadiation ell z x) =
        rescalePhysicalRadiation ell g := by
    funext x
    have heq := actual_Hartree_overlap_cutoff_physical_scale
      ell R x hell hR
    change actualOneLayerInnerOverlapCutoff R x *
        ((Real.sqrt ell : ℂ) * z (ell * x)) =
      (Real.sqrt ell : ℂ) *
        (actualOneLayerInnerOverlapCutoff (ell * R) (ell * x) * z (ell * x))
    rw [heq]
    ring
  have hScaleIdentity :
      complexRadialHartreeNonlinearity
          (fun x => actualOneLayerInnerOverlapCutoff R x *
            rescalePhysicalRadiation ell z x) r -
        actualOneLayerInnerOverlapCutoff R r *
          complexRadialHartreeNonlinearity
            (rescalePhysicalRadiation ell z) r =
      ((ell ^ 2 * Real.sqrt ell : ℝ) : ℂ) *
        (complexRadialHartreeNonlinearity g (ell * r) -
          actualOneLayerInnerOverlapCutoff (ell * R) (ell * r) *
            complexRadialHartreeNonlinearity z (ell * r)) := by
    rw [hScaledField,
      actual_Hartree_critical_scaled_nonlinearity ell r hell g,
      actual_Hartree_critical_scaled_nonlinearity ell r hell z,
      actual_Hartree_overlap_cutoff_physical_scale ell R r hell hR]
    ring
  calc
    ‖complexRadialHartreeNonlinearity
          (fun x => actualOneLayerInnerOverlapCutoff R x *
            rescalePhysicalRadiation ell z x) r -
      actualOneLayerInnerOverlapCutoff R r *
        complexRadialHartreeNonlinearity
          (rescalePhysicalRadiation ell z) r‖ =
        (ell ^ 2 * Real.sqrt ell) *
          ‖complexRadialHartreeNonlinearity g (ell * r) -
            actualOneLayerInnerOverlapCutoff (ell * R) (ell * r) *
              complexRadialHartreeNonlinearity z (ell * r)‖ := by
                rw [hScaleIdentity, norm_mul, Complex.norm_real,
                  Real.norm_eq_abs,
                  abs_of_nonneg (by positivity : 0 ≤ ell ^ 2 * Real.sqrt ell)]
    _ ≤ (ell ^ 2 * Real.sqrt ell) *
          (2 * radialHartreeRowBoundConstant * D * B ^ 3) :=
      mul_le_mul_of_nonneg_left hAtOne (by positivity)
    _ = (2 * radialHartreeRowBoundConstant * D * B ^ 3) *
          ell ^ 2 * Real.sqrt ell := by ring

end HBL.TypeIIDynamicSelection
