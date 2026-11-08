import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingOriginalSourceFromScaledOrbit
import HBL.TypeIIDynamicSelection.ActualHartreeFullInteractionTimeFromOrbit
import Mathlib.Tactic

/-!
# Original moving Kummer Hartree source time derivative from one physical orbit

The actual source is F0(s,r)=-a(s)^2 S_Hartree(ell(s),c(s),z(s);a(s)*r),
where S_Hartree is the SAME original mixed three-Riesz nonlocal
interaction. The exact critical scaling identity transports it to
one source at a fixed normalized radial point, built from
  V_a,c(s,x)=sqrt(a(s))*V_c(s,a(s)*x),
  Z_a,ell(s,x)=sqrt(a(s))*sqrt(ell(s))*z(s,ell(s)*a(s)*x).

The original source derivative is DERIVED by:
  (1) differentiating the FULL original mixed/pure/core Riesz potentials
      on these two physical scaled time-dependent fields, with their
      exact quartic time velocities and genuine logarithmic kernel;
  (2) differentiating the actual local cubic multiplier of each;
  (3) applying the precise critical-scaling identity to remove
      the moving observation a(s)*r and the exact sqrt(a(s)) prefactor.

Neither the derivative of F0 nor of any of the three Riesz potentials
is assumed. All analytic hypotheses concern the original physical
C1 real/complex fields and their actual kernel-weighted integrable
time-velocity majorants. The final blow-up rate is not assumed.
This fixed-r source calculus does not prove the O(s^(-9/4))
four-piece Hartree PDE residual or original weighted norms.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual real core of the original Hartree interaction after
exact physical energy-critical scaling by the Kummer parameter. -/
def actualHartreeTrueTwoStageScaledCore
    (a c : ℝ → ℝ) (t r : ℝ) : ℝ :=
  actualHartreeCriticalScaledRealCore (a t)
    (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c t)) (c t)) r

/-- The ORIGINAL complex radiation after both actual physical
critical rescalings, with no truncation of its nonlocal density. -/
def actualHartreeTrueTwoStageScaledRadiation
    (a ell : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (t r : ℝ) : ℂ :=
  rescalePhysicalRadiation (a t)
    (rescalePhysicalRadiation (ell t) (z t)) r

theorem actual_Hartree_original_Kummer_source_time_from_full_scaled_orbit
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (dV : ℝ → ℝ → ℝ) (dZ : ℝ → ℝ → ℂ)
    (r s adot : ℝ) (hr : 0 < r)
    (hA : HasDerivAt a adot s) (ha : 0 < a s)
    (I : Set ℝ) (hI : I ∈ 𝓝 s) (hs : s ∈ I)
    (hV : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => actualHartreeTrueTwoStageScaledCore
        a c x rho) (dV t rho) t)
    (hZRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (actualHartreeTrueTwoStageScaledRadiation
        a ell z x rho).re) (dZ t rho).re t)
    (hZIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (actualHartreeTrueTwoStageScaledRadiation
        a ell z x rho).im) (dZ t rho).im t)
    (hZat : HasDerivAt
      (fun t => actualHartreeTrueTwoStageScaledRadiation a ell z t r)
      (dZ s r) s)
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
    HasDerivAt
      (fun t => actualHartreeLaplacianScaledKummerSource
        (a t) (ell t) (c t) (z t) r)
      (let hDot :=
        actualHartreeFullInteractionTimeVelocity
          (actualHartreeTrueTwoStageScaledCore a c) dV
          (actualHartreeTrueTwoStageScaledRadiation a ell z) dZ
          ((2 * Real.pi * hartreeKappa / r) *
            ∫ rho in Ioi (0 : ℝ),
              actualHartreeMixedRieszTimeVelocity
                (actualHartreeTrueTwoStageScaledCore a c) dV
                (actualHartreeTrueTwoStageScaledRadiation a ell z) dZ r s rho)
          ((2 * Real.pi * hartreeKappa / r) *
            ∫ rho in Ioi (0 : ℝ),
              actualHartreeRieszQuarticTimeVelocity
                (actualHartreeTrueTwoStageScaledRadiation a ell z) dZ r s rho)
          ((2 * Real.pi * hartreeKappa / r) *
            ∫ rho in Ioi (0 : ℝ),
              actualHartreeRieszQuarticTimeVelocity
                (fun τ x =>
                  (actualHartreeTrueTwoStageScaledCore a c τ x : ℂ))
                (fun τ x => (dV τ x : ℂ)) r s rho)
          s r;
       -( ((adot / (2 * Real.sqrt (a s)) : ℝ) : ℂ) /
            (((Real.sqrt (a s) : ℝ) : ℂ) ^ 2)) *
          actualHartreeTrueCriticallyScaledOriginalInteraction a ell c z s r +
        (((Real.sqrt (a s) : ℝ) : ℂ)⁻¹) * hDot) s := by
  let V : ℝ → ℝ → ℝ := actualHartreeTrueTwoStageScaledCore a c
  let Z : ℝ → ℝ → ℂ := actualHartreeTrueTwoStageScaledRadiation a ell z
  let mDot : ℝ :=
    (2 * Real.pi * hartreeKappa / r) *
      ∫ rho in Ioi (0 : ℝ),
        actualHartreeMixedRieszTimeVelocity V dV Z dZ r s rho
  let zDot : ℝ :=
    (2 * Real.pi * hartreeKappa / r) *
      ∫ rho in Ioi (0 : ℝ),
        actualHartreeRieszQuarticTimeVelocity Z dZ r s rho
  let vDot : ℝ :=
    (2 * Real.pi * hartreeKappa / r) *
      ∫ rho in Ioi (0 : ℝ),
        actualHartreeRieszQuarticTimeVelocity
          (fun τ x => (V τ x : ℂ))
          (fun τ x => (dV τ x : ℂ)) r s rho
  let D : ℂ := actualHartreeFullInteractionTimeVelocity
    V dV Z dZ mDot zDot vDot s r
  have hFull :=
    actual_Hartree_full_interaction_time_from_one_physical_orbit
      V dV Z dZ r s hr I hI hs
      hV hZRe hZIm hZat
      hMixMeas hMixInt hMixDotMeas BM hBM hMixBound
      hZMeas hZInt hZDotMeas BZ hBZ hZBound
      hVMeas hVInt hVDotMeas BV hBV hVBound
  have hSame : 
      (fun t => actualHartreeTrueCriticallyScaledOriginalInteraction
        a ell c z t r) =
      (fun t => actualOneLayerInteractionOnly V Z t r) := by
    funext t
    rfl
  have hScaled : HasDerivAt
      (fun t => actualHartreeTrueCriticallyScaledOriginalInteraction
        a ell c z t r) D s := by
    rw [hSame]
    simpa only [D, mDot, zDot, vDot] using hFull
  have hOriginal :=
    actual_Hartree_original_moving_source_derivative_from_scaled_orbit
      a ell c z s r adot hA ha D hScaled
  simpa only [D, V, Z, mDot, zDot, vDot] using hOriginal

end HBL.TypeIIDynamicSelection
