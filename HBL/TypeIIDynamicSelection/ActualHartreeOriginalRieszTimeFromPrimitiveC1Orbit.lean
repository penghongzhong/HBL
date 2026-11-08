import HBL.TypeIIDynamicSelection.ActualHartreePhysicalScaledCoreRadiationTimeProducer
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceTimeFromPhysicalScaledOrbit
import Mathlib.Tactic

/-!
# Remove independently assumed two-stage core and radiation derivatives

For the GENUINE three-term inverse-square quartic Hartree Riesz source
F0(s,r) = a(s)^2 * Interaction(V_c(s),Z_ell(s))(a(s)*r),
the already verified original three logarithmic Riesz integral
differentiation requires real-core and complex-radiation pointwise
time tangents. This proof PRODUCES every one of those tangents from
actual differentiable a,c,ell and the physical (time,radius) C1
differential of z, not from separate assumptions about the scaled
core or scaled radiation.

The only remaining analytic inputs are original kernel-weighted
integrability and domination of mixed, pure-radiation and pure-core
quartic time-velocity integrals along the same orbit. The physical
time velocities dV and dZ are DEFINITIONALLY fixed to the derived
two-stage critical chain-rule expressions; no independent velocity
function can be chosen.

This gives an actual source-time derivative existentially, with its
value explicitly computed by the original full-three-Riesz theorem.
It is not a proof of uniform O(s^(-9/4)) original four-piece residual.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_original_Riesz_source_time_from_primitive_physical_C1
    (a ell c adot ellDot cdot : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (Dz : ℝ → ℝ → (ℝ × ℝ →L[ℝ] ℂ))
    (dV : ℝ → ℝ → ℝ) (dZ : ℝ → ℝ → ℂ)
    (hdV : dV = actualHartreeTwoStageRealCoreTimeVelocity a c adot cdot)
    (hdZ : dZ = actualHartreeTwoStageComplexRadiationTimeVelocity
      a ell adot ellDot z Dz)
    (r s : ℝ) (hr : 0 < r)
    (I : Set ℝ) (hI : I ∈ 𝓝 s) (hs : s ∈ I)
    (hA : ∀ t ∈ I, HasDerivAt a (adot t) t)
    (hEll : ∀ t ∈ I, HasDerivAt ell (ellDot t) t)
    (hc : ∀ t ∈ I, HasDerivAt c (cdot t) t)
    (ha : ∀ t ∈ I, 0 < a t)
    (hEllPos : ∀ t ∈ I, 0 < ell t)
    (hZ : ∀ t ∈ I, ∀ rho : ℝ, 0 < rho →
      HasFDerivAt (fun p : ℝ × ℝ => z p.1 p.2)
        (Dz t rho) (t, ell t * (a t * rho)))
    (hMixMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeMixedRieszTimeIntegrand
          (actualHartreeTrueTwoStageScaledCore a c)
          (actualHartreeTrueTwoStageScaledRadiation a ell z) r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hMixInt : IntegrableOn
      (actualHartreeMixedRieszTimeIntegrand
        (actualHartreeTrueTwoStageScaledCore a c)
        (actualHartreeTrueTwoStageScaledRadiation a ell z) r s)
      (Ioi (0 : ℝ)))
    (hMixDotMeas : AEStronglyMeasurable
      (actualHartreeMixedRieszTimeVelocity
        (actualHartreeTrueTwoStageScaledCore a c) dV
        (actualHartreeTrueTwoStageScaledRadiation a ell z) dZ r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (BM : ℝ → ℝ)
    (hBM : IntegrableOn BM (Ioi (0 : ℝ)))
    (hMixBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeMixedRieszTimeVelocity
        (actualHartreeTrueTwoStageScaledCore a c) dV
        (actualHartreeTrueTwoStageScaledRadiation a ell z) dZ r t rho|
        ≤ BM rho)
    (hZMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeRieszQuarticTimeIntegrand
          (actualHartreeTrueTwoStageScaledRadiation a ell z) r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZInt : IntegrableOn
      (actualHartreeRieszQuarticTimeIntegrand
        (actualHartreeTrueTwoStageScaledRadiation a ell z) r s)
      (Ioi (0 : ℝ)))
    (hZDotMeas : AEStronglyMeasurable
      (actualHartreeRieszQuarticTimeVelocity
        (actualHartreeTrueTwoStageScaledRadiation a ell z) dZ r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (BZ : ℝ → ℝ) (hBZ : IntegrableOn BZ (Ioi (0 : ℝ)))
    (hZBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeRieszQuarticTimeVelocity
        (actualHartreeTrueTwoStageScaledRadiation a ell z) dZ r t rho|
          ≤ BZ rho)
    (hVMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeRieszQuarticTimeIntegrand
          (fun τ rho =>
            (actualHartreeTrueTwoStageScaledCore a c τ rho : ℂ)) r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hVInt : IntegrableOn
      (actualHartreeRieszQuarticTimeIntegrand
        (fun τ rho =>
          (actualHartreeTrueTwoStageScaledCore a c τ rho : ℂ)) r s)
      (Ioi (0 : ℝ)))
    (hVDotMeas : AEStronglyMeasurable
      (actualHartreeRieszQuarticTimeVelocity
        (fun τ rho =>
          (actualHartreeTrueTwoStageScaledCore a c τ rho : ℂ))
        (fun τ rho => (dV τ rho : ℂ)) r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (BV : ℝ → ℝ) (hBV : IntegrableOn BV (Ioi (0 : ℝ)))
    (hVBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeRieszQuarticTimeVelocity
        (fun τ x => (actualHartreeTrueTwoStageScaledCore a c τ x : ℂ))
        (fun τ x => (dV τ x : ℂ)) r t rho|
          ≤ BV rho) :
    ∃ Fdot : ℂ,
      HasDerivAt
        (fun t => actualHartreeLaplacianScaledKummerSource
          (a t) (ell t) (c t) (z t) r) Fdot s := by
  obtain ⟨hVraw, hZraw⟩ :=
    actual_Hartree_one_orbit_scaled_core_and_radiation_tangents
      a ell c adot ellDot cdot z Dz I
      hA hEll hc ha hEllPos hZ
  have hVactual : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => actualHartreeTrueTwoStageScaledCore a c x rho)
        (dV t rho) t := by
    intro rho hrho t ht
    rw [hdV]
    exact hVraw rho hrho t ht
  have hZactual : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => actualHartreeTrueTwoStageScaledRadiation
        a ell z x rho) (dZ t rho) t := by
    intro rho hrho t ht
    rw [hdZ]
    exact hZraw rho hrho t ht
  have hZRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (actualHartreeTrueTwoStageScaledRadiation
        a ell z x rho).re) (dZ t rho).re t := by
    intro rho hrho t ht
    have hMap : HasDerivAt (fun _ : ℝ => Complex.reCLM)
        (0 : ℂ →L[ℝ] ℝ) t := hasDerivAt_const t Complex.reCLM
    have h := hMap.clm_apply (hZactual rho hrho t ht)
    simpa only [zero_apply, zero_add, Complex.reCLM_apply] using h
  have hZIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (actualHartreeTrueTwoStageScaledRadiation
        a ell z x rho).im) (dZ t rho).im t := by
    intro rho hrho t ht
    have hMap : HasDerivAt (fun _ : ℝ => Complex.imCLM)
        (0 : ℂ →L[ℝ] ℝ) t := hasDerivAt_const t Complex.imCLM
    have h := hMap.clm_apply (hZactual rho hrho t ht)
    simpa only [zero_apply, zero_add, Complex.imCLM_apply] using h
  have hZat : HasDerivAt
      (fun t => actualHartreeTrueTwoStageScaledRadiation a ell z t r)
      (dZ s r) s := hZactual r hr s hs
  exact ⟨_,
    actual_Hartree_original_Kummer_source_time_from_full_scaled_orbit
      a ell c z dV dZ r s (adot s) hr
      (hA s hs) (ha s hs) I hI hs
      hVactual hZRe hZIm hZat
      hMixMeas hMixInt hMixDotMeas BM hBM hMixBound
      hZMeas hZInt hZDotMeas BZ hBZ hZBound
      hVMeas hVInt hVDotMeas BV hBV hVBound⟩

end HBL.TypeIIDynamicSelection
