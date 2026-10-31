import HBL.TypeIIDynamicSelection.ActualOneLayerPDEResidual
import HBL.TypeIIDynamicSelection.ActualRadiation3DMoment
import HBL.MonopoleMovingCutoffTime
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Manuscript 2.12: actual phase and monopole parameter tangents

The original PDE has two genuine time-dependent modulation directions.
This module identifies their exact pointwise coefficients in the ACTUAL
complex Hartree radial profile, using the true amplitude-dependent
moving cutoff and the phase rotation. The annular chi' term is retained
even when c(s) crosses zero. No formal "tangent=tangent" statement,
preset blowup speed, or hypothetical abstract PDE residual is used.

The later physical-clock specialization uses the true three-dimensional
radiation moment for c_g; the phase specialization uses the proven
kinematic synchronized phase. Neither proves the four-region nonlinear
weighted residual cancellation in the full manuscript 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual complex phased profile: the real moving-cutoff monopole
plus entire complex radiation, rotated by its physical phase. -/
def actualPhasedMovingMonopoleWithRadiation
    (c gamma : ℝ → ℝ) (Z : ℝ → ℝ → ℂ) (t r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (gamma t : ℂ)) *
    ((monopolePerturbedRadialProfile
       (monopoleQuadraticRadius (c t)) (c t) r : ℂ) + Z t r)

/-- TRUE two-directional time-derivative: phase velocity times the
actual whole profile plus amplitude velocity times the full moving
monopole tangent. The derivative of the moving cutoff (chi') is not
discarded in the annulus and the statement includes c(s)=0. -/
theorem actual_phased_moving_monopole_two_parameter_tangent
    (c gamma : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {s r cs gs : ℝ} {dz : ℂ}
    (hc : HasDerivAt c cs s)
    (hg : HasDerivAt gamma gs s)
    (hZ : HasDerivAt (fun t : ℝ => Z t r) dz s) :
    HasDerivAt
      (fun t => actualPhasedMovingMonopoleWithRadiation c gamma Z t r)
      (Complex.exp (Complex.I * (gamma s : ℂ)) *
        ((Complex.I * (gs : ℂ)) *
           ((monopolePerturbedRadialProfile
              (monopoleQuadraticRadius (c s)) (c s) r : ℂ) + Z s r) +
         ((cs * monopoleRadialProfile r *
           (1 - cutoff (|c s| * r / 4) -
             (|c s| * r / 4) * deriv cutoff (|c s| * r / 4)) : ℝ) : ℂ) +
         dz)) s := by
  have hgC : HasDerivAt
      (fun t : ℝ => (gamma t : ℂ)) (gs : ℂ) s :=
    hg.ofReal_comp
  have harg : HasDerivAt
      (fun t : ℝ => Complex.I * (gamma t : ℂ))
      (Complex.I * (gs : ℂ)) s :=
    hgC.const_mul Complex.I
  have he : HasDerivAt
      (fun t : ℝ => Complex.exp (Complex.I * (gamma t : ℂ)))
      (Complex.exp (Complex.I * (gamma s : ℂ)) *
        (Complex.I * (gs : ℂ))) s :=
    harg.cexp
  have hprofile : HasDerivAt
      (fun t : ℝ =>
        (monopolePerturbedRadialProfile
           (monopoleQuadraticRadius (c t)) (c t) r : ℂ))
      ((cs * monopoleRadialProfile r *
         (1 - cutoff (|c s| * r / 4) -
           (|c s| * r / 4) * deriv cutoff (|c s| * r / 4)) : ℝ) : ℂ) s :=
    (monopoleMovingCutoffTime_hasDerivAt hc r).ofReal_comp
  have hsum := hprofile.add hZ
  have hproduct := he.mul hsum
  convert hproduct using 1
  · rfl
  · simp only [Pi.add_apply]
    ring

/-- The actual Hartree PDE residual contains precisely the identified
two phase/amplitude speed directions. The spatial Laplacian, full
seven-power nonlocal Hartree term and scaling drift are retained
UNCHANGED. This is an equation for the genuine source, not an arbitrary
linear functional asserted to be the projected tangent. -/
theorem actual_phased_moving_monopole_Hartree_PDE_tangent
    (c gamma : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {s r cs gs : ℝ} {dz : ℂ}
    (b omega : ℝ)
    (hc : HasDerivAt c cs s)
    (hg : HasDerivAt gamma gs s)
    (hZ : HasDerivAt (fun t : ℝ => Z t r) dz s) :
    complexRadialRenormalizedResidual
      (actualPhasedMovingMonopoleWithRadiation c gamma Z) b omega s r =
      Complex.I *
        (Complex.exp (Complex.I * (gamma s : ℂ)) *
          ((Complex.I * (gs : ℂ)) *
             ((monopolePerturbedRadialProfile
                (monopoleQuadraticRadius (c s)) (c s) r : ℂ) + Z s r) +
           ((cs * monopoleRadialProfile r *
             (1 - cutoff (|c s| * r / 4) -
               (|c s| * r / 4) * deriv cutoff (|c s| * r / 4)) : ℝ) : ℂ) +
           dz)) +
      complexRadialLaplacian
        (actualPhasedMovingMonopoleWithRadiation c gamma Z s) r +
      complexRadialHartreeNonlinearity
        (actualPhasedMovingMonopoleWithRadiation c gamma Z s) r +
      Complex.I * (b : ℂ) *
        complexRadialDilation
          (actualPhasedMovingMonopoleWithRadiation c gamma Z s) r +
      (omega : ℂ) * actualPhasedMovingMonopoleWithRadiation c gamma Z s r := by
  unfold complexRadialRenormalizedResidual
  rw [(actual_phased_moving_monopole_two_parameter_tangent
    c gamma Z hc hg hZ).deriv]

end HBL.TypeIIDynamicSelection
