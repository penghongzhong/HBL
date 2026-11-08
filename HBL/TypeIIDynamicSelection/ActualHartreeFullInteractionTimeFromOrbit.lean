import HBL.TypeIIDynamicSelection.ActualHartreeFullNonlocalInteractionTimeDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeMixedRieszTimeDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeRadialRieszTimeDerivative
import Mathlib.Tactic

/-!
# Actual full original 3D Hartree nonlocal interaction time derivative
# directly produced from one physical real monopole and complex radiation orbit

The full source is the SAME original three-term inverse-square quartic
logarithmic Hartree interaction:
   P_mix*C(V+z) + P_z*(C(V+z)-C(z)) + P_V*(C(V+z)-C(V)).
The time derivatives of the ALL THREE original Riesz potentials and
ALL THREE genuine local cubic multipliers are produced (not assumed)
from V_s, z_s via the strict original radial dominated-integral
and local-cubic differentiation theorems.

Each majorant below is a concrete integrable bound for one actual
logarithmic-kernel weighted quartic velocity. Nothing equivalent to
the full interaction time derivative is postulated as a new axiom,
free regional source, synthetic order packet or fixed Type-II rate.

These original physical high-regularity C1 and integral-dominating
hypotheses still require a genuine producer on the final Hartree PDE
trajectory. The observation radius r is fixed here; the remaining
moving-observer and moving Kummer basis derivatives and the
weighted O(s^(-9/4)) full four-piece residual are not claimed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_full_interaction_time_from_one_physical_orbit
    (V dV : ℝ → ℝ → ℝ) (z dz : ℝ → ℝ → ℂ)
    (r s : ℝ) (hr : 0 < r) (I : Set ℝ)
    (hI : I ∈ 𝓝 s) (hs : s ∈ I)
    (hV : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => V x rho) (dV t rho) t)
    (hZRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).re) (dz t rho).re t)
    (hZIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).im) (dz t rho).im t)
    (hZat : HasDerivAt (fun t => z t r) (dz s r) s)
    -- True physical MIXED quartic logarithmic Riesz majorant.
    (hMixMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeMixedRieszTimeIntegrand V z r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hMixInt : IntegrableOn
      (actualHartreeMixedRieszTimeIntegrand V z r s)
      (Ioi (0 : ℝ)))
    (hMixDotMeas : AEStronglyMeasurable
      (actualHartreeMixedRieszTimeVelocity V dV z dz r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (BM : ℝ → ℝ)
    (hBM : IntegrableOn BM (Ioi (0 : ℝ)))
    (hMixBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeMixedRieszTimeVelocity V dV z dz r t rho| ≤ BM rho)
    -- True physical radiation self-quartic Riesz majorant.
    (hZMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeRieszQuarticTimeIntegrand z r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZInt : IntegrableOn
      (actualHartreeRieszQuarticTimeIntegrand z r s)
      (Ioi (0 : ℝ)))
    (hZDotMeas : AEStronglyMeasurable
      (actualHartreeRieszQuarticTimeVelocity z dz r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (BZ : ℝ → ℝ)
    (hBZ : IntegrableOn BZ (Ioi (0 : ℝ)))
    (hZBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeRieszQuarticTimeVelocity z dz r t rho| ≤ BZ rho)
    -- True physical real-core quartic logarithmic Riesz majorant.
    (hVMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeRieszQuarticTimeIntegrand
          (fun τ rho => (V τ rho : ℂ)) r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hVInt : IntegrableOn
      (actualHartreeRieszQuarticTimeIntegrand
        (fun τ rho => (V τ rho : ℂ)) r s)
      (Ioi (0 : ℝ)))
    (hVDotMeas : AEStronglyMeasurable
      (actualHartreeRieszQuarticTimeVelocity
        (fun τ rho => (V τ rho : ℂ))
        (fun τ rho => (dV τ rho : ℂ)) r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (BV : ℝ → ℝ)
    (hBV : IntegrableOn BV (Ioi (0 : ℝ)))
    (hVBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeRieszQuarticTimeVelocity
        (fun τ x => (V τ x : ℂ))
        (fun τ x => (dV τ x : ℂ)) r t rho| ≤ BV rho) :
    HasDerivAt
      (fun t => actualOneLayerInteractionOnly V z t r)
      (actualHartreeFullInteractionTimeVelocity V dV z dz
        ((2 * Real.pi * hartreeKappa / r) *
          ∫ rho in Ioi (0 : ℝ),
            actualHartreeMixedRieszTimeVelocity V dV z dz r s rho)
        ((2 * Real.pi * hartreeKappa / r) *
          ∫ rho in Ioi (0 : ℝ),
            actualHartreeRieszQuarticTimeVelocity z dz r s rho)
        ((2 * Real.pi * hartreeKappa / r) *
          ∫ rho in Ioi (0 : ℝ),
            actualHartreeRieszQuarticTimeVelocity
              (fun τ x => (V τ x : ℂ))
              (fun τ x => (dV τ x : ℂ)) r s rho)
        s r) s := by
  have hMix :=
    actual_Hartree_mixed_Riesz_potential_time_derivative_from_orbit
      V dV z dz r s hr I hI hMixMeas hMixInt
      hMixDotMeas BM hBM hMixBound hV hZRe hZIm
  have hZ :=
    actual_Hartree_radial_Riesz_potential_time_derivative_from_radiation
      z dz r s hr I hI hZMeas hZInt hZDotMeas
      BZ hBZ hZBound hZRe hZIm
  have hVRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (V x rho : ℂ).re)
        (dV t rho : ℂ).re t := by
    intro rho hrho t ht
    simpa only [Complex.ofReal_re] using hV rho hrho t ht
  have hVIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (V x rho : ℂ).im)
        (dV t rho : ℂ).im t := by
    intro rho _ t _
    simpa only [Complex.ofReal_im] using (hasDerivAt_const t (0 : ℝ))
  have hCore :=
    actual_Hartree_radial_Riesz_potential_time_derivative_from_radiation
      (fun τ rho => (V τ rho : ℂ))
      (fun τ rho => (dV τ rho : ℂ))
      r s hr I hI hVMeas hVInt hVDotMeas
      BV hBV hVBound hVRe hVIm
  exact actual_Hartree_full_nonlocal_interaction_time_derivative
    V dV z dz s r _ _ _
    (hV r hr s hs) hZat hMix hZ hCore

end HBL.TypeIIDynamicSelection
