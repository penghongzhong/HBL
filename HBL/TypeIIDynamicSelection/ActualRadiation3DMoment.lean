import HBL.PhysicalRadial3LocalPotential
import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import Mathlib.Tactic

/-!
# EXACT 3D radial Hartree source moment, not a postulated radial formula

In dimension three the manuscript weighted radiation moment is
  m0[z] = ∫_{R³} |x|^(-2) |z(|x|)|^4 dx.
The true 4*pi radial reduction follows from the already proved
physicalRadial3_integral (Haar polar integration with exact unit-ball
measure), not from a newly assumed change-of-measure axiom.

The integrand at the origin is totalized as zero, irrelevant since a
singleton has Lebesgue measure zero. All statements are actual equalities
of Lean's Lebesgue integrals, and can later be combined with the
established radiation weighted L2 and quartic integrability.

This directly matches the original manuscript slow monopole coefficient:
  c_g = kappa_H * ell * m0[z], ell = lambda^(-1).
No terminal modulation speed or Type II orbit is assumed or constructed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Metric
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual physical THREE-DIMENSIONAL inverse-square radiation
quartic moment, not a formal 1D radial stand-in. -/
def actualPhysicalInverseSquareMoment (z : ℝ → ℂ) : ℝ :=
  ∫ x : PhysicalRadialSpace3,
    (‖x‖ ^ 2)⁻¹ * ‖z ‖x‖‖ ^ 4

/-- Exact three-dimensional radial reduction of the entire radiation
source; the 4 pi factor is a theorem about the actual Haar measure. -/
theorem actual_physical_inverse_square_radial_reduction
    (z : ℝ → ℂ) :
    actualPhysicalInverseSquareMoment z =
      radialPhysicalQuarticMoment z := by
  unfold actualPhysicalInverseSquareMoment
  rw [physicalRadial3_integral
    (fun r : ℝ => (r ^ 2)⁻¹ * ‖z r‖ ^ 4)]
  unfold radialPhysicalQuarticMoment
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change r ^ 2 * ((r ^ 2)⁻¹ * ‖z r‖ ^ 4) = ‖z r‖ ^ 4
  have hrpos : (0 : ℝ) < r := hr
  have hrne : r ≠ 0 := ne_of_gt hrpos
  field_simp [hrne]

/-- The actual 3D source moment is precisely the coefficient selected
by the whole rescaled radiation Hartree center on the physical clock. -/
theorem actual_whole_radiation_center_eq_physical_threeD_moment
    (ell : ℝ) (hEll : 0 < ell) (z : ℝ → ℂ) :
    actualRadiationCenter (rescalePhysicalRadiation ell z) =
      hartreeKappa * ell * actualPhysicalInverseSquareMoment z := by
  rw [actualRadiationCenter_equals_physical_slow_coefficient ell hEll z,
    actual_physical_inverse_square_radial_reduction]

end HBL.TypeIIDynamicSelection
