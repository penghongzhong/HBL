import HBL.TypeIIDynamicSelection.ActualHartreeRadialPDECriticalScaling
import HBL.TypeIIDynamicSelection.ActualPhasedSpatialFlatness
import HBL.MonopoleComplexResidual
import Mathlib.Tactic

/-!
# Original Hartree PDE: EXACT critical-scale and complex-phase covariance

The nonlinear PDE term is NOT merely a local cubic. The physical
inverse-square Hartree potential P[z] times |z|² z has energy-critical
spatial scaling:
  Z_ell(r)=sqrt(ell) z(ell*r),
  N(Z_ell)(r)=ell² sqrt(ell) N(z)(ell*r).

This follows from the actual radial Riesz logarithmic integral's
change-of-variables theorem and the exact local cubic scaling.

For a unit complex phase e^(-i gamma) the complete nonlocal Hartree
term transforms covariantly. The combined identity retains the
original K=|x|^{-2}, coupling kappa_H=3/pi² and BOTH physical scale
and phase, rather than a replacement polynomial model.

Neither a blowup speed nor a renormalized radiation PDE is assumed
or proved here. The next obligation is the time/spatial chain
rule along a genuine regular Hartree flow.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The physical critical rescaling of the local cubic multiplier is
exactly ell*sqrt(ell), with no approximation. -/
theorem actual_Hartree_critical_rescaled_local_cubic
    (ell r : ℝ) (hell : 0 < ell) (z : ℝ → ℂ) :
    actualWholeRadiationLocalCubic (rescalePhysicalRadiation ell z) r =
      ((ell * Real.sqrt ell : ℝ) : ℂ) *
        actualWholeRadiationLocalCubic z (ell * r) := by
  have hSq :
      ‖rescalePhysicalRadiation ell z r‖ ^ 2 =
        ell * ‖z (ell * r)‖ ^ 2 := by
    unfold rescalePhysicalRadiation
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg ell), mul_pow,
      Real.sq_sqrt hell.le]
  unfold actualWholeRadiationLocalCubic
  rw [hSq]
  unfold rescalePhysicalRadiation
  push_cast
  ring

/-- Crucial full NONLOCAL Hartree PDE scaling, including the
original quartic Riesz convolution, for arbitrary complex z. -/
theorem actual_Hartree_critical_scaled_nonlinearity
    (ell r : ℝ) (hell : 0 < ell) (z : ℝ → ℂ) :
    complexRadialHartreeNonlinearity (rescalePhysicalRadiation ell z) r =
      ((ell ^ 2 * Real.sqrt ell : ℝ) : ℂ) *
        complexRadialHartreeNonlinearity z (ell * r) := by
  have hP := actual_Hartree_critical_radiation_Riesz_scaling ell r hell z
  have hC := actual_Hartree_critical_rescaled_local_cubic ell r hell z
  unfold complexRadialHartreeNonlinearity
  change (radialHartreePotential
      (fun rho => ‖rescalePhysicalRadiation ell z rho‖ ^ 4) r : ℂ) *
      actualWholeRadiationLocalCubic (rescalePhysicalRadiation ell z) r = _
  rw [hP, hC]
  unfold actualWholeRadiationLocalCubic complexRadialHartreeNonlinearity
  push_cast
  ring

/-- The physical complex phase used in the manuscript, without
imposing an arbitrary time-dependent modulation speed. -/
def actualHartreeUnitPhase (gamma : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((-gamma : ℝ) : ℂ))

theorem actual_Hartree_unit_phase_norm (gamma : ℝ) :
    ‖actualHartreeUnitPhase gamma‖ = 1 := by
  exact actual_Hartree_unit_complex_phase gamma

/-- Full Hartree phase covariance, with its true nonlocal quartic
convolution, not an imaginary-channel sign convention. -/
theorem actual_Hartree_nonlinearity_phase_covariant
    (gamma r : ℝ) (z : ℝ → ℂ) :
    complexRadialHartreeNonlinearity
      (fun rho => actualHartreeUnitPhase gamma * z rho) r =
    actualHartreeUnitPhase gamma *
      complexRadialHartreeNonlinearity z r := by
  have hNorm (rho : ℝ) :
      ‖actualHartreeUnitPhase gamma * z rho‖ = ‖z rho‖ := by
    rw [norm_mul, actual_Hartree_unit_phase_norm, one_mul]
  have hDensity :
      (fun rho => ‖actualHartreeUnitPhase gamma * z rho‖ ^ 4) =
        (fun rho => ‖z rho‖ ^ 4) := by
    funext rho
    rw [hNorm]
  unfold complexRadialHartreeNonlinearity
  rw [hDensity, hNorm]
  ring

/-- Combined exact real time-dependent critical-scale and complex
phase covariance at each frozen renormalized time. -/
theorem actual_Hartree_phased_critical_scaled_nonlinearity
    (ell gamma r : ℝ) (hell : 0 < ell) (z : ℝ → ℂ) :
    complexRadialHartreeNonlinearity
      (fun rho => actualHartreeUnitPhase gamma *
        rescalePhysicalRadiation ell z rho) r =
    actualHartreeUnitPhase gamma *
      (((ell ^ 2 * Real.sqrt ell : ℝ) : ℂ) *
        complexRadialHartreeNonlinearity z (ell * r)) := by
  rw [actual_Hartree_nonlinearity_phase_covariant,
    actual_Hartree_critical_scaled_nonlinearity ell r hell z]

end HBL.TypeIIDynamicSelection
