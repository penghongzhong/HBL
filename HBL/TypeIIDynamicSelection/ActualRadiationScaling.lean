import HBL.TypeIIDynamicSelection.ActualRadiationCenter
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Original HBL slow monopole coefficient from the ENTIRE radiation

The original paper defines c_g = kappa_H * lambda^{-1} * m_0[z_g],
where m_0[z] = ∫_(R^3) |z(x)|^4/|x|^2 dx.
For radial z the moment is 4*pi*∫_(0,∞)|z(r)|^4 dr.

If ell=lambda^{-1}>0, the physical rescaling of a radial complex
radiation field is Z_ell(y)=sqrt(ell)*z(ell*y), exactly the energy-critical
3D Schrödinger scaling used by the paper. The TRUE entire-radiation
Hartree center coefficient satisfies

  C[Z_ell] = kappa_H * ell * m_0^rad[z].

The proof uses the actual Ioi change of variables; it neither prescribes
an asymptotic lambda exponent nor imposes remote support. This is the
physical link the previously studied exterior-only source did not provide.

The identification of the radial 1D moment with the 3D integral via the
polar integration map remains a separately tracked radial-lift boundary.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The exact energy-critical pullback of the entire physical radial
radiation under concentrated length ell=1/lambda. -/
def rescalePhysicalRadiation (ell : ℝ) (z : ℝ → ℂ) (r : ℝ) : ℂ :=
  (Real.sqrt ell : ℂ) * z (ell * r)

/-- The radial representation of the physical inverse-square weighted
3D quartic moment, before invoking the polar change of variables. -/
def radialPhysicalQuarticMoment (z : ℝ → ℂ) : ℝ :=
  4 * Real.pi * ∫ rho in Ioi (0 : ℝ), ‖z rho‖ ^ 4

/-- Exactly two scale factors survive the quartic pointwise density. -/
theorem rescalePhysicalRadiation_quartic
    (ell : ℝ) (hEll : 0 ≤ ell) (z : ℝ → ℂ) (r : ℝ) :
    ‖rescalePhysicalRadiation ell z r‖ ^ 4 =
      ell ^ 2 * ‖z (ell * r)‖ ^ 4 := by
  unfold rescalePhysicalRadiation
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg ell), mul_pow]
  have hs : (Real.sqrt ell) ^ 4 = ell ^ 2 := by
    calc
      (Real.sqrt ell) ^ 4 = ((Real.sqrt ell) ^ 2) ^ 2 := by ring
      _ = ell ^ 2 := by rw [Real.sq_sqrt hEll]
  rw [hs]

/-- TRUE physical center mass of the rescaled entire radiation is
linear in the length ell=1/lambda, with no terminal rate assumption. -/
theorem actualRadiationCenter_rescaling
    (ell : ℝ) (hEll : 0 < ell) (z : ℝ → ℂ) :
    actualRadiationCenter (rescalePhysicalRadiation ell z) =
      ell * actualRadiationCenter z := by
  have hpoint (r : ℝ) := rescalePhysicalRadiation_quartic ell hEll.le z r
  have hint :
      (∫ r in Ioi (0 : ℝ), ‖rescalePhysicalRadiation ell z r‖ ^ 4) =
      ell ^ 2 * ∫ r in Ioi (0 : ℝ), ‖z (ell * r)‖ ^ 4 := by
    simp_rw [hpoint]
    rw [integral_const_mul]
  have hchange :
      (∫ r in Ioi (0 : ℝ), ‖z (ell * r)‖ ^ 4) =
      ell⁻¹ * ∫ r in Ioi (0 : ℝ), ‖z r‖ ^ 4 := by
    simpa only [mul_zero, smul_eq_mul] using
      (integral_comp_mul_left_Ioi (fun r : ℝ => ‖z r‖ ^ 4) 0 hEll)
  unfold actualRadiationCenter radialHartreeCenter
  rw [hint, hchange]
  field_simp [hEll.ne']

/-- Exact radial version of the manuscript coefficient
c_g(s)=kappa_H lambda(s)^{-1} m_0[z_g(t(s))], with the actual
rescaled field and no prescribed limiting exponent. -/
theorem actualRadiationCenter_equals_physical_slow_coefficient
    (ell : ℝ) (hEll : 0 < ell) (z : ℝ → ℂ) :
    actualRadiationCenter (rescalePhysicalRadiation ell z) =
      hartreeKappa * ell * radialPhysicalQuarticMoment z := by
  rw [actualRadiationCenter_rescaling ell hEll z]
  unfold actualRadiationCenter radialHartreeCenter radialPhysicalQuarticMoment
  ring

end HBL.TypeIIDynamicSelection
