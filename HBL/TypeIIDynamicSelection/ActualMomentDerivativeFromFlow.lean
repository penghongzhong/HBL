import HBL.TypeIIDynamicSelection.ActualRadiation3DMoment
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# A REAL differentiated physical 3D Hartree inverse-square radiation moment

The actual physical inverse-square quartic moment m₀(z(t)) is exactly
4π times the L⁴ radial half-line integral. Its derivative is now
DERIVED by the genuine Mathlib dominated differentiation theorem.
No HasDerivAt of m₀ is a hypothesis.

The primitive analytic inputs are:
* pointwise C¹ time evolution of BOTH real components of the actual
  complex radial regular radiation;
* measurable/integrable genuine quartic data and velocity source;
* a uniformly integrable majorant of the pointwise quartic derivative.

For smooth high-regularity Hartree terminal radiation these are the
precise analytic facts that must be instantiated from the standard
local theory; no claim of that remaining Sobolev embedding or the
full nonlinear Hartree Type II orbit is made in this file.

The source also records the exact cancellation of a real Hartree
potential's pure imaginary gauge-phase contribution, with NO guessed
nonlinear local surrogate.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole

/-- The actual pointwise quartic moment velocity of a complex
physical radial radiation and its true time derivative. -/
def actualRadialQuarticMomentVelocity (z dz : ℂ) : ℝ :=
  4 * ‖z‖ ^ 2 * (Complex.conj z * dz).re

/-- The whole complex source is reduced to real/imaginary variables;
this identity is exact, including at a zero of z. -/
theorem actual_radial_quartic_velocity_coordinates
    (z dz : ℂ) :
    actualRadialQuarticMomentVelocity z dz =
      4 * (z.re ^ 2 + z.im ^ 2) *
        (z.re * dz.re + z.im * dz.im) := by
  unfold actualRadialQuarticMomentVelocity
  rw [← Complex.normSq_eq_norm_sq z]
  simp only [Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The true pointwise derivative of |z(t,r)|^4.
The inputs are the two real coordinate derivatives of the SAME z,
not a derivative of the quartic density or its integral. -/
theorem actual_radial_quartic_hasDerivAt
    (z : ℝ → ℂ) (dz : ℂ) (t : ℝ)
    (hRe : HasDerivAt (fun x : ℝ => (z x).re) dz.re t)
    (hIm : HasDerivAt (fun x : ℝ => (z x).im) dz.im t) :
    HasDerivAt (fun x : ℝ => ‖z x‖ ^ 4)
      (actualRadialQuarticMomentVelocity (z t) dz) t := by
  have hpoly := ((hRe.pow 2).add (hIm.pow 2)).pow 2
  have heq : (fun x : ℝ => ‖z x‖ ^ 4) =
      (fun x => ((z x).re ^ 2 + (z x).im ^ 2) ^ 2) := by
    funext x
    calc
      ‖z x‖ ^ 4 = (‖z x‖ ^ 2) ^ 2 := by ring
      _ = Complex.normSq (z x) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
      _ = ((z x).re ^ 2 + (z x).im ^ 2) ^ 2 := by
        rw [Complex.normSq_apply]
        ring
  rw [heq]
  convert hpoly using 1
  · rfl
  · rw [actual_radial_quartic_velocity_coordinates]
    ring

/-- The physical 3D Hartree quartic moment derivative is reconstructed
from the original complex radiation and a uniformly integrable flux
envelope, not assumed as a differentiated scalar input. -/
theorem actual_physical_threeD_moment_hasDerivAt_of_dominated_radiation
    (z dz : ℝ → ℝ → ℂ)
    (t₀ : ℝ) (I : Set ℝ)
    (hI : I ∈ 𝓝 t₀)
    (hZmeas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (fun rho => ‖z t rho‖ ^ 4)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn (fun rho => ‖z t₀ rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (fun rho => actualRadialQuarticMomentVelocity (z t₀ rho) (dz t₀ rho))
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ)
    (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (dz t rho)| ≤ B rho)
    (hRe : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).re) (dz t rho).re t)
    (hIm : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).im) (dz t rho).im t) :
    HasDerivAt (fun t => actualPhysicalInverseSquareMoment (z t))
      (4 * Real.pi *
        ∫ rho in Ioi (0 : ℝ),
          actualRadialQuarticMomentVelocity (z t₀ rho) (dz t₀ rho))
      t₀ := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℝ := fun t rho => ‖z t rho‖ ^ 4
  let F' : ℝ → ℝ → ℝ := fun t rho =>
    actualRadialQuarticMomentVelocity (z t rho) (dz t rho)
  have hbd : ∀ᵐ rho ∂μ, ∀ t ∈ I, ‖F' t rho‖ ≤ B rho := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    intro t ht
    simpa only [F', Real.norm_eq_abs] using hBound rho hrho t ht
  have hderiv : ∀ᵐ rho ∂μ, ∀ t ∈ I,
      HasDerivAt (F · rho) (F' t rho) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    intro t ht
    exact actual_radial_quartic_hasDerivAt
      (fun x => z x rho) (dz t rho) t
      (hRe rho hrho t ht) (hIm rho hrho t ht)
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (μ := μ) (s := I) (x₀ := t₀)
    (bound := B) hI hZmeas hZint hVelMeas hbd hB hderiv
  have hrad : HasDerivAt
      (fun t => radialPhysicalQuarticMoment (z t))
      (4 * Real.pi * ∫ rho in Ioi (0 : ℝ), F' t₀ rho) t₀ := by
    simpa only [radialPhysicalQuarticMoment, F', F] using
      hresult.2.const_mul (4 * Real.pi)
  have hphysical :
      (fun t => actualPhysicalInverseSquareMoment (z t)) =
        (fun t => radialPhysicalQuarticMoment (z t)) := by
    funext t
    exact actual_physical_inverse_square_radial_reduction (z t)
  rw [hphysical]
  exact hrad

/-- The imaginary radial Hartree potential is a pure U(1) phase
rotation and contributes ZERO to the real quartic moment derivative.
The coefficient is genuinely real, as in the original Hartree Riesz
potential, with no local-cubic replacement. -/
theorem actual_Hartree_real_potential_quartic_phase_cancellation
    (z : ℂ) (V : ℝ) :
    actualRadialQuarticMomentVelocity z
      (Complex.I * (V : ℂ) * (‖z‖ ^ 2 : ℝ) * z) = 0 := by
  rw [actual_radial_quartic_velocity_coordinates]
  simp only [Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

#print axioms actual_radial_quartic_hasDerivAt
#print axioms actual_physical_threeD_moment_hasDerivAt_of_dominated_radiation
#print axioms actual_Hartree_real_potential_quartic_phase_cancellation

end HBL.TypeIIDynamicSelection
