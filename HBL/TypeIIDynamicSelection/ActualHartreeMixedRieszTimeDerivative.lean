import HBL.TypeIIDynamicSelection.ActualHartreeRadialRieszTimeDerivative
import HBL.TypeIIDynamicSelection.ActualWholeRadiationSelfCubic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-!
# The genuine MIXED quartic Hartree Riesz density and potential time derivative

The actual full mixed 3D quartic density of one real monopole V and one
complex radial radiation z is exactly
   M(V,z) = |V+z|^4 - |V|^4 - |z|^4.
The real and imaginary time-velocity components of z and the real
velocity of V determine its derivative. Nothing about the derivative
of the full quartic density is assumed.

For one FIXED observation radius r>0, the derivative of the original
radial inverse-square logarithmic Hartree potential I[M(V,z)](r)
is then derived by Mathlib's dominated parametric integral theorem,
using the true radial kernel and the physical mixed quartic velocity.

This bridges a key nonlocal mixed quartic cross-density term of the
retained HBL §2.13 PDE. Integrability of the actual weighted velocity
and pointwise C1 of physical V/z remain visible analytic inputs;
there is no specified Type-II blow-up law or source-smallness axiom.
Moving observation radius, original physical source rescaling,
changed cubic multipliers and full all-four-piece residual are
separate obligations, not inferred from this theorem.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Velocity of the original mixed quartic density, with all three
actual physical contributions and real monopole derivative retained. -/
def actualHartreeMixedQuarticTimeVelocity
    (V dV : ℝ → ℝ → ℝ) (z dz : ℝ → ℝ → ℂ)
    (t rho : ℝ) : ℝ :=
  actualRadialQuarticMomentVelocity
    ((V t rho : ℂ) + z t rho) ((dV t rho : ℂ) + dz t rho) -
  actualRadialQuarticMomentVelocity
    (V t rho : ℂ) (dV t rho : ℂ) -
  actualRadialQuarticMomentVelocity (z t rho) (dz t rho)

/-- Direct physical calculation from V_s and z_s, not an assumed mixed
density time derivative. It remains valid at zero monopole/radiation. -/
theorem actual_Hartree_mixed_quartic_time_derivative_from_real_complex_orbit
    (V dV : ℝ → ℝ → ℝ) (z dz : ℝ → ℝ → ℂ)
    (s rho : ℝ)
    (hV : HasDerivAt (fun t => V t rho) (dV s rho) s)
    (hRe : HasDerivAt (fun t => (z t rho).re) (dz s rho).re s)
    (hIm : HasDerivAt (fun t => (z t rho).im) (dz s rho).im s) :
    HasDerivAt
      (fun t => actualWholeRadiationMixedQuartic (V t) (z t) rho)
      (actualHartreeMixedQuarticTimeVelocity V dV z dz s rho) s := by
  have hTotalRe :
      HasDerivAt (fun t => ((V t rho : ℂ) + z t rho).re)
        ((dV s rho : ℂ) + dz s rho).re s := by
    simpa only [Complex.add_re, Complex.ofReal_re, Pi.add_apply] using hV.add hRe
  have hTotalIm :
      HasDerivAt (fun t => ((V t rho : ℂ) + z t rho).im)
        ((dV s rho : ℂ) + dz s rho).im s := by
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hIm
  have hCoreRe :
      HasDerivAt (fun t => (V t rho : ℂ).re)
        (dV s rho : ℂ).re s := by
    simpa only [Complex.ofReal_re] using hV
  have hCoreIm :
      HasDerivAt (fun t => (V t rho : ℂ).im)
        (dV s rho : ℂ).im s := by
    simpa only [Complex.ofReal_im] using (hasDerivAt_const s (0 : ℝ))
  have hTotal :=
    actual_radial_quartic_hasDerivAt
      (fun t => (V t rho : ℂ) + z t rho)
      ((dV s rho : ℂ) + dz s rho) s hTotalRe hTotalIm
  have hCore :=
    actual_radial_quartic_hasDerivAt
      (fun t => (V t rho : ℂ))
      (dV s rho : ℂ) s hCoreRe hCoreIm
  have hRadiation :=
    actual_radial_quartic_hasDerivAt
      (fun t => z t rho) (dz s rho) s hRe hIm
  have hMixed := (hTotal.sub hCore).sub hRadiation
  convert hMixed using 1
  · funext t
    simp only [actualWholeRadiationMixedQuartic, Pi.sub_apply]
  · rfl

/-- The actual fixed-observer logarithmic Hartree integrand of the
MIXED quartic original physical density. -/
def actualHartreeMixedRieszTimeIntegrand
    (V : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (r t rho : ℝ) : ℝ :=
  rho * hartreeRadialLog r rho *
    actualWholeRadiationMixedQuartic (V t) (z t) rho

/-- Its true parameter time derivative, with no local approximation. -/
def actualHartreeMixedRieszTimeVelocity
    (V dV : ℝ → ℝ → ℝ) (z dz : ℝ → ℝ → ℂ)
    (r t rho : ℝ) : ℝ :=
  rho * hartreeRadialLog r rho *
    actualHartreeMixedQuarticTimeVelocity V dV z dz t rho

/-- Differentiate the entire original nonlocal mixed Hartree Riesz
potential. No HasDerivAt for this potential or the mixed quartic
density is part of the assumptions. -/
theorem actual_Hartree_mixed_Riesz_potential_time_derivative_from_orbit
    (V dV : ℝ → ℝ → ℝ) (z dz : ℝ → ℝ → ℂ)
    (r s : ℝ) (_hr : 0 < r)
    (I : Set ℝ) (hI : I ∈ 𝓝 s)
    (hMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeMixedRieszTimeIntegrand V z r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hInt : IntegrableOn
      (actualHartreeMixedRieszTimeIntegrand V z r s)
      (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (actualHartreeMixedRieszTimeVelocity V dV z dz r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ)
    (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeMixedRieszTimeVelocity V dV z dz r t rho| ≤ B rho)
    (hV : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => V x rho) (dV t rho) t)
    (hRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).re) (dz t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).im) (dz t rho).im t) :
    HasDerivAt
      (fun t => radialHartreePotential
        (actualWholeRadiationMixedQuartic (V t) (z t)) r)
      ((2 * Real.pi * hartreeKappa / r) *
        ∫ rho in Ioi (0 : ℝ),
          actualHartreeMixedRieszTimeVelocity V dV z dz r s rho) s := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℝ :=
    fun t rho => actualHartreeMixedRieszTimeIntegrand V z r t rho
  let F' : ℝ → ℝ → ℝ :=
    fun t rho => actualHartreeMixedRieszTimeVelocity V dV z dz r t rho
  have hbd : ∀ᵐ rho ∂μ, ∀ t ∈ I, ‖F' t rho‖ ≤ B rho := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    intro t ht
    simpa only [F', Real.norm_eq_abs] using hBound rho hrho t ht
  have hderiv : ∀ᵐ rho ∂μ, ∀ t ∈ I,
      HasDerivAt (F · rho) (F' t rho) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    intro t ht
    have hMixed := actual_Hartree_mixed_quartic_time_derivative_from_real_complex_orbit
      V dV z dz t rho
      (hV rho hrho t ht) (hRe rho hrho t ht) (hIm rho hrho t ht)
    have hWeighted := hMixed.const_mul (rho * hartreeRadialLog r rho)
    simpa only [F, F', actualHartreeMixedRieszTimeIntegrand,
      actualHartreeMixedRieszTimeVelocity] using hWeighted
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (μ := μ) (s := I) (x₀ := s)
    (bound := B) hI hMeas hInt hVelMeas hbd hB hderiv
  simpa only [radialHartreePotential,
    actualHartreeMixedRieszTimeIntegrand,
    actualHartreeMixedRieszTimeVelocity, F, F'] using
    hresult.2.const_mul (2 * Real.pi * hartreeKappa / r)

end HBL.TypeIIDynamicSelection
