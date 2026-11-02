import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import HBL.RadialHartreePotential
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Genuine radial inverse-square Hartree Riesz potential under critical scaling

A missing input in original profile 2.12 is the EXACT nonlocal
scaling law, required to turn the CitedHighRegularityHartreeLocalTheory
physical solution into a solution of the renormalized Hartree PDE.
We derive it for the actual radial logarithmic Riesz kernel, not an
artificial local cubic or a prescribed source.

  Z_ell(r) = sqrt(ell) z(ell r),
  P[Z_ell](r) = ell * P[z](ell r)

where P includes kappa_H = 3/pi². Only ell > 0 is assumed. The
change of variables is the actual Lebesgue half-line integral formula.
A separate radial time/phase chain-rule bridge remains necessary before
the full true-flow residual cancellation is available without a
high-level radiation-PDE hypothesis.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The genuine radial Hartree logarithm has exactly degree-zero
simultaneous spatial scaling at every point, including the diagonal. -/
theorem actual_Hartree_radial_log_scale_invariant
    (ell r rho : ℝ) (hell : 0 < ell) :
    hartreeRadialLog (ell * r) (ell * rho) =
      hartreeRadialLog r rho := by
  by_cases hd : r = rho
  · subst rho
    simp [hartreeRadialLog]
  · have habs : |r - rho| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hd)
    unfold hartreeRadialLog
    have hnum : ell * r + ell * rho = ell * (r + rho) := by ring
    have hden : |ell * r - ell * rho| = ell * |r - rho| := by
      rw [← mul_sub, abs_mul, abs_of_pos hell]
    rw [hnum, hden]
    congr 1
    field_simp [hell.ne', habs]

/-- Critical fourth-power density scaling for the full radial Hartree
operator. The exact half-line change-of-variable is internal to the proof. -/
theorem actual_Hartree_radial_potential_scale_quartic_density
    (ell r : ℝ) (hell : 0 < ell) (F : ℝ → ℝ) :
    radialHartreePotential
       (fun rho => ell ^ 2 * F (ell * rho)) r =
      ell * radialHartreePotential F (ell * r) := by
  let G : ℝ → ℝ := fun rho =>
    rho * hartreeRadialLog (ell * r) rho * F rho
  have hchange :
      (∫ rho in Ioi (0 : ℝ), G (ell * rho)) =
        ell⁻¹ * ∫ rho in Ioi (0 : ℝ), G rho := by
    simpa only [mul_zero, smul_eq_mul] using
      (integral_comp_mul_left_Ioi G 0 hell)
  have hInt :
      (∫ rho in Ioi (0 : ℝ),
        rho * hartreeRadialLog r rho *
          (ell ^ 2 * F (ell * rho))) =
        ∫ rho in Ioi (0 : ℝ), G rho := by
    calc
      _ = ∫ rho in Ioi (0 : ℝ), ell * G (ell * rho) := by
        apply integral_congr_ae
        filter_upwards with rho
        dsimp [G]
        rw [actual_Hartree_radial_log_scale_invariant ell r rho hell]
        ring
      _ = ell * (∫ rho in Ioi (0 : ℝ), G (ell * rho)) := by
        rw [integral_const_mul]
      _ = ell * (ell⁻¹ * ∫ rho in Ioi (0 : ℝ), G rho) := by rw [hchange]
      _ = ∫ rho in Ioi (0 : ℝ), G rho := by
        field_simp [hell.ne']
  unfold radialHartreePotential
  rw [hInt]
  by_cases hr : r = 0
  · subst r
    simp
  · have her : ell * r ≠ 0 := mul_ne_zero hell.ne' hr
    change (2 * Real.pi * hartreeKappa / r) *
        (∫ rho in Ioi (0 : ℝ), G rho) =
      ell * ((2 * Real.pi * hartreeKappa / (ell * r)) *
        (∫ rho in Ioi (0 : ℝ), G rho))
    field_simp [hell.ne', hr, her]

/-- The true complex energy-critical pullback, with its actual
quartic Riesz density and original normalizing constant, satisfies
the exact nonlocal potential rescaling identity. -/
theorem actual_Hartree_critical_radiation_Riesz_scaling
    (ell r : ℝ) (hell : 0 < ell) (z : ℝ → ℂ) :
    radialHartreePotential
      (fun rho => ‖rescalePhysicalRadiation ell z rho‖ ^ 4) r =
      ell * radialHartreePotential (fun rho => ‖z rho‖ ^ 4)
        (ell * r) := by
  have hdensity :
      (fun rho => ‖rescalePhysicalRadiation ell z rho‖ ^ 4) =
        (fun rho => ell ^ 2 * ‖z (ell * rho)‖ ^ 4) := by
    funext rho
    exact rescalePhysicalRadiation_quartic ell hell.le z rho
  rw [hdensity]
  exact actual_Hartree_radial_potential_scale_quartic_density
    ell r hell (fun rho => ‖z rho‖ ^ 4)

end HBL.TypeIIDynamicSelection
