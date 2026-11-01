import HBL.TypeIIDynamicSelection.ActualMomentPDEFlux
import HBL.TypeIIDynamicSelection.ActualMomentCutoffTransport
import Mathlib.Tactic

/-!
# Actual PDE-driven positive-length gain for the original moving Hartree cutoff

For a FIXED nonzero regular terminal radiation, the original whole-radiation
3D inverse-square moment m(t) may be strictly positive near its terminal
time. This module derives the precise O(ell^2) material-transport gain
from the genuine physical moment and its actual PDE Laplacian flux.

No limiting blowup exponent or artificial constant monopole charge is
prescribed. The first statement needs only the derived moment differentiability;
the second gets that differentiability from the ORIGINAL Hartree PDE,
using the strictly verified dominated-differentiation terminal.

A single point in the genuine cutoff-transition annulus is considered;
the fixed smooth cutoff derivative bound, transition support, and positivity
of the physical terminal moment are explicit, ordinary analytic hypotheses.
This is an actual weighted SOURCE estimate, not the full three-region
Hartree/Fredholm/Kummer matching in original manuscript 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The complete physical radial Laplacian flux, already rigorously
identified by the source-level original Hartree PDE theorem. -/
def actualMomentLaplacianFlux (u : ℝ → ℂ) : ℝ :=
  -16 * Real.pi * ∫ rho in Ioi (0 : ℝ),
    ‖u rho‖ ^ 2 *
      ((u rho).re * (complexRadialLaplacian u rho).im -
        (u rho).im * (complexRadialLaplacian u rho).re)

/-- Physical moving cutoff transport, on the REAL transition annulus.
The bare b*c drift cancels. Since c=kappa_H ell m and c*r/4<=2,
the remaining term is O(ell^2) times the actual relative moment flux.
No upper or lower time exponent for ell is assumed. -/
theorem actualMomentInnerCutoff_transport_length_gain
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    {s dm : ℝ} (r Cχ : ℝ)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hMoment3D : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t)) dm (time s))
    (hMomentPos : 0 < actualPhysicalInverseSquareMoment (z (time s)))
    (hr : 0 ≤ r)
    (htransition :
      actualPhysicalRadiationMonopole ell z time s * r / 4 ≤ 2)
    (hChi :
      |deriv cutoff
        (actualPhysicalRadiationMonopole ell z time s * r / 4)| ≤ Cχ) :
    |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
        b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
      (2 * (ell s) ^ 2 *
        (|dm| / radialPhysicalQuarticMoment (z (time s)))) * Cχ := by
  let c : ℝ := actualPhysicalRadiationMonopole ell z time s
  let m : ℝ := radialPhysicalQuarticMoment (z (time s))
  have hm : 0 < m := by
    dsimp [m]
    rw [actual_physical_inverse_square_radial_reduction] at hMomentPos
    exact hMomentPos
  have hC : c = hartreeKappa * ell s * m := by
    exact actualRadiationCenter_equals_physical_slow_coefficient
      (ell s) hEllPos (z (time s))
  have hK : 0 ≤ hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hcoefPos : 0 ≤ hartreeKappa * (ell s) ^ 3 * r / 4 := by
    positivity
  have hCr : c * r ≤ 8 := by
    change c * r / 4 ≤ 2 at htransition
    linarith
  have hcoeffMul :
      (hartreeKappa * (ell s) ^ 3 * r / 4) * m ≤
        2 * (ell s) ^ 2 := by
    calc
      _ = (c * r) * ((ell s) ^ 2 / 4) := by rw [hC]; ring
      _ ≤ 8 * ((ell s) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right hCr (by positivity)
      _ = 2 * (ell s) ^ 2 := by ring
  have hcoef :
      hartreeKappa * (ell s) ^ 3 * r / 4 ≤
        2 * (ell s) ^ 2 / m :=
    (le_div_iff₀ hm).2 hcoeffMul
  have hchiNonneg : 0 ≤ Cχ :=
    (abs_nonneg _).trans hChi
  have hMomentRadial : HasDerivAt
      (fun t => radialPhysicalQuarticMoment (z t)) dm (time s) := by
    simpa only [actual_physical_inverse_square_radial_reduction] using hMoment3D
  have htransport := actualMomentInnerCutoff_material_derivative
    ell b z time r hEll hEllPos hTime hMomentRadial
  have hAbs :
      |-(hartreeKappa * (ell s) ^ 3 * dm * r / 4)| =
        (hartreeKappa * (ell s) ^ 3 * r / 4) * |dm| := by
    rw [abs_neg]
    have hid : hartreeKappa * (ell s) ^ 3 * dm * r / 4 =
        (hartreeKappa * (ell s) ^ 3 * r / 4) * dm := by ring
    rw [hid, abs_mul, abs_of_nonneg hcoefPos]
  change |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
        b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
      (2 * (ell s) ^ 2 * (|dm| / m)) * Cχ
  calc
    _ = (hartreeKappa * (ell s) ^ 3 * r / 4) * |dm| *
          |deriv cutoff (c * r / 4)| := by
      rw [htransport, abs_mul, hAbs]
    _ ≤ (hartreeKappa * (ell s) ^ 3 * r / 4) * |dm| * Cχ :=
      mul_le_mul_of_nonneg_left hChi
        (mul_nonneg hcoefPos (abs_nonneg dm))
    _ ≤ (2 * (ell s) ^ 2 / m * |dm|) * Cχ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (abs_nonneg dm)) hchiNonneg
    _ = (2 * (ell s) ^ 2 * (|dm| / m)) * Cχ := by ring

/-- The SAME gain, with the moment derivative itself now derived
from the exact original Hartree radial PDE and genuine dominated
differentiation under the three-dimensional physical moment integral.
In particular NO HasDerivAt(moment) appears among these assumptions. -/
theorem actual_Hartree_PDE_cutoff_transport_length_gain
    (ell b : ℝ → ℝ) (z zt : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    {s : ℝ} (r Cχ : ℝ)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (I : Set ℝ)
    (hI : I ∈ 𝓝 (time s))
    (hZmeas : ∀ᶠ t in 𝓝 (time s),
      AEStronglyMeasurable (fun rho => ‖z t rho‖ ^ 4)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn
      (fun rho => ‖z (time s) rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (fun rho =>
        actualRadialQuarticMomentVelocity (z (time s) rho) (zt (time s) rho))
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ)
    (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (zt t rho)| ≤ B rho)
    (hRe : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).re) (zt t rho).re t)
    (hIm : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).im) (zt t rho).im t)
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt (time s) rho = Complex.I *
        (complexRadialLaplacian (z (time s)) rho +
          complexRadialHartreeNonlinearity (z (time s)) rho))
    (hMomentPos : 0 < actualPhysicalInverseSquareMoment (z (time s)))
    (hr : 0 ≤ r)
    (htransition :
      actualPhysicalRadiationMonopole ell z time s * r / 4 ≤ 2)
    (hChi :
      |deriv cutoff
        (actualPhysicalRadiationMonopole ell z time s * r / 4)| ≤ Cχ) :
    |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
        b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
      (2 * (ell s) ^ 2 *
        (|actualMomentLaplacianFlux (z (time s))| /
          radialPhysicalQuarticMoment (z (time s)))) * Cχ := by
  have hMoment : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t))
      (actualMomentLaplacianFlux (z (time s))) (time s) := by
    exact actual_physical_threeD_Hartree_radiation_moment_PDE_flux
      z zt (time s) I hI hZmeas hZint hVelMeas B hB
      hBound hRe hIm hPDE
  exact actualMomentInnerCutoff_transport_length_gain
    ell b z time r Cχ hEll hEllPos hTime hMoment
    hMomentPos hr htransition hChi

#print axioms actualMomentInnerCutoff_transport_length_gain
#print axioms actual_Hartree_PDE_cutoff_transport_length_gain

end HBL.TypeIIDynamicSelection
