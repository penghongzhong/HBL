import HBL.TypeIIDynamicSelection.ActualOneLayerSpatialOverlapGain
import HBL.KummerFrozenAnnulus
import Mathlib.Tactic

/-!
# Physical Kummer annulus: exact C2 cutoff commutator for canonical localization

Original 2.12 cannot add independent homogeneous Kummer coefficients:
both normalized endpoint Wronskians already fix them. The correct
ONE-ORBIT correction is a canonical localized Kummer Green source,
where overlap derivatives generate a controlled PDE commutator.

For the TRUE frozen physical Kummer coefficient
  a(r)=2/r+i*r/2,  b(mu,theta)=theta+i*(1/4-mu),
define L_(mu,theta)u = u'' + a(r)u' + b(mu,theta)u.
The exact ORIGINAL inner cutoff chi_R(r)=1-cutoff(r/R)
gives the pointwise identity
  L(chi_R*u)-chi_R*L(u)
      =2*chi_R'*u' + (chi_R''+a(r)*chi_R')*u.

This is a real, source-level physical Kummer identity, neither an
abstract RegionalSolver nor a guessed positive gain. Boundary
parameter/remote/whole-Hartree nonlinear terms remain separate
before original 2.12 can be certified.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.Kummer

/-- Genuine frozen Hartree physical Kummer operator at positive
radius; retains the imaginary i*r/2 drift coefficient and the
two real spectral/modulation parameters. -/
def actualHartreeFrozenKummerRadialApply
    (mu theta : ℝ) (u : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv (deriv u) r + frozenFirstCoeff r * deriv u r +
    frozenZeroCoeff mu theta * u r

/-- Exact commutator of the ORIGINAL smooth moving spatial cutoff
with the physical frozen Kummer operator. A localized canonical
Green solution needs these genuine two derivative costs;
there is no free homogeneous matching parameter. -/
theorem actual_Hartree_frozen_Kummer_actual_cutoff_commutator
    (mu theta R r : ℝ) (hR : R ≠ 0)
    (u : ℝ → ℂ)
    (hu : ∀ x : ℝ, DifferentiableAt ℝ u x)
    (hu2 : DifferentiableAt ℝ (deriv u) r) :
    actualHartreeFrozenKummerRadialApply mu theta
        (fun x => actualOneLayerInnerOverlapCutoff R x * u x) r -
      actualOneLayerInnerOverlapCutoff R r *
        actualHartreeFrozenKummerRadialApply mu theta u r =
      2 * deriv (actualOneLayerInnerOverlapCutoff R) r * deriv u r +
        (deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r +
          frozenFirstCoeff r *
            deriv (actualOneLayerInnerOverlapCutoff R) r) * u r := by
  let chi : ℝ → ℂ := actualOneLayerInnerOverlapCutoff R
  have hChi (x : ℝ) : DifferentiableAt ℝ chi x :=
    (actual_one_layer_overlap_cutoff_hasDerivAt R x).differentiableAt
  have hChi2 : DifferentiableAt ℝ (deriv chi) r :=
    (actual_one_layer_overlap_cutoff_deriv_hasDerivAt R r hR).differentiableAt
  have hFirst :
      deriv (fun x => chi x * u x) r =
        deriv chi r * u r + chi r * deriv u r :=
    ((hChi r).hasDerivAt.mul (hu r).hasDerivAt).deriv
  have hRad :=
    actual_one_layer_radial_Laplacian_cutoff_commutator
      chi u r hChi hu hChi2 hu2
  change actualHartreeFrozenKummerRadialApply mu theta
        (fun x => chi x * u x) r -
      chi r * actualHartreeFrozenKummerRadialApply mu theta u r =
      2 * deriv chi r * deriv u r +
        (deriv (deriv chi) r +
          frozenFirstCoeff r * deriv chi r) * u r
  calc
    _ = (complexRadialLaplacian (fun x => chi x * u x) r -
          chi r * complexRadialLaplacian u r) +
        (Complex.I * (r : ℂ) / 2) *
          (deriv (fun x => chi x * u x) r -
            chi r * deriv u r) := by
          unfold actualHartreeFrozenKummerRadialApply
            complexRadialLaplacian frozenFirstCoeff
          ring
    _ = 2 * deriv chi r * deriv u r +
        (deriv (deriv chi) r +
          frozenFirstCoeff r * deriv chi r) * u r := by
          rw [hRad, hFirst]
          unfold frozenFirstCoeff
          ring

end HBL.TypeIIDynamicSelection
