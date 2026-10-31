import HBL.TypeIIDynamicSelection.ActualMomentCutoffTransport
import HBL.TypeIIDynamicSelection.ActualRadiation3DMoment
import HBL.MonopoleMovingCutoffTime
import Mathlib.Tactic

/-!
# Original Hartree monopole profile: actual physical 3D moment time derivative

The amplitude is the genuine complete radial Hartree three-dimensional
inverse-square quartic radiation moment, evaluated at the actual physical
clock. The profile is exactly the originally defined
monopolePerturbedRadialProfile, including at c=0.

The theorem derives c_s from the true physical 3D moment and chain rule;
it does not insert an arbitrary c_s, impose an asymptotic rate, or claim
the full PDE one-layer cancellation. Source-moment differentiability
remains a high-regularity flow obligation stated explicitly.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology ContDiff

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual moving monopole *profile* whose amplitude is selected by
the whole physical 3D inverse-square Hartree radiation moment. -/
def actualMomentMonopoleProfile
    (ell : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    (s r : ℝ) : ℝ :=
  monopolePerturbedRadialProfile
    (monopoleQuadraticRadius (actualPhysicalRadiationMonopole ell z time s))
    (actualPhysicalRadiationMonopole ell z time s) r

/-- Exact physical time tangent including the moving radial cutoff.
The coefficient is output by the genuine 3D radiation integral, not
supplied as independent modulation data. -/
theorem actual_moment_monopole_profile_threeD_hasDerivAt
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    {s dm : ℝ} (r : ℝ)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hMoment3D : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t)) dm (time s)) :
    HasDerivAt (fun t => actualMomentMonopoleProfile ell z time t r)
      ((-(b s * actualPhysicalRadiationMonopole ell z time s) +
          hartreeKappa * (ell s) ^ 3 * dm) *
        monopoleRadialProfile r *
        (1 - cutoff (actualPhysicalRadiationMonopole ell z time s * r / 4) -
          (actualPhysicalRadiationMonopole ell z time s * r / 4) *
            deriv cutoff (actualPhysicalRadiationMonopole ell z time s * r / 4))) s := by
  have hcoef := actual_physical_threeD_radiation_slow_coefficient_hasDerivAt
    ell b z time hEll hEllPos hTime hMoment3D
  have hnonneg : 0 ≤ actualPhysicalRadiationMonopole ell z time s :=
    actualRadiationCenter_nonneg _
  have hprofile := monopoleMovingCutoffTime_hasDerivAt hcoef r
  simpa only [actualMomentMonopoleProfile, abs_of_nonneg hnonneg] using hprofile

/-- On the actual strict core the complete 3D-moment-driven amplitude
tangent is precisely c_s times the already constructed radial monopole;
the moving cutoff derivative vanishes, even if c=0. -/
theorem actual_moment_monopole_core_threeD_hasDerivAt
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    {s dm r : ℝ}
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hMoment3D : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t)) dm (time s))
    (hcore : actualPhysicalRadiationMonopole ell z time s * r / 4 < 1) :
    HasDerivAt (fun t => actualMomentMonopoleProfile ell z time t r)
      ((-(b s * actualPhysicalRadiationMonopole ell z time s) +
          hartreeKappa * (ell s) ^ 3 * dm) *
        monopoleRadialProfile r) s := by
  have hcoef := actual_physical_threeD_radiation_slow_coefficient_hasDerivAt
    ell b z time hEll hEllPos hTime hMoment3D
  have hnonneg : 0 ≤ actualPhysicalRadiationMonopole ell z time s :=
    actualRadiationCenter_nonneg _
  have hcore' :
      |actualPhysicalRadiationMonopole ell z time s| * r / 4 < 1 := by
    simpa only [abs_of_nonneg hnonneg] using hcore
  simpa only [actualMomentMonopoleProfile] using
    (monopoleMovingCutoffTime_core_hasDerivAt hcoef hcore')

end HBL.TypeIIDynamicSelection
