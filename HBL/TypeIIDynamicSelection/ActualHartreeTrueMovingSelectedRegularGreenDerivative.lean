import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingAdjustedSourceDerivative
import HBL.TypeIIDynamicSelection.ActualOriginGreenSourceTimeDerivative
import Mathlib.Tactic

/-!
# One genuinely time-varying Hartree source: selected regular Green derivative

The actual original full 3D quartic Riesz source, its two genuine moving
modulation source directions, and the Cramer-selected real pair are placed
inside the ORIGINAL regular Green coefficient integral. This module reuses
Mathlib's dominated parametric interval integral theorem through the
previously strict origin Green source derivative producer.

The derivative of the adjusted source is *derived* from differentiability
of the original three sources and the two actual compatibility columns;
no derivative of the adjusted source or the selected speeds is assumed.
The domination of the physical time-derivative Green density, source
regularity, and the original Cramer column derivative budgets remain
visible analytic hypotheses. The Green basis and lower endpoint are
fixed in this theorem. The genuine moving basis and moving lower endpoint
must be treated separately for the full 3D PDE parametrix.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology Interval
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeTrueMovingAdjustedSourceDot
    (a _ell c : ℝ → ℝ) (_z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ)
    (Fdot Sdot Pdot : ℝ → ℝ → ℂ) (t r : ℝ) : ℂ :=
  let pb : ℝ → ℝ := fun u =>
    (actualRealCramerCorrection (b u) (w u) (Z u)).1
  let pw : ℝ → ℝ := fun u =>
    (actualRealCramerCorrection (b u) (w u) (Z u)).2
  Fdot t r -
    (((deriv pb t : ℝ) : ℂ) * actualMomentLockedScaledScaleSource (a t) (c t) r +
      (pb t : ℂ) * Sdot t r) -
    (((deriv pw t : ℝ) : ℂ) * actualMomentLockedScaledPhaseSource (a t) (c t) r +
      (pw t : ℂ) * Pdot t r)

/-- A true moving Hartree physical source, with its actual selected speed,
has a differentiable regular-origin Green integral. The only assumptions on
the derivative source are those of the original dominated-integral lemma. -/
theorem actual_Hartree_true_moving_selected_regular_Green_hasDerivAt
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r0 B s : ℝ)
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z bdot wdot Zdot : ℝ → ℂ)
    (Fdot Sdot Pdot : ℝ → ℝ → ℂ)
    (T : Set ℝ) (bound : ℝ → ℝ)
    (hT : T ∈ 𝓝 s)
    (hB : 0 < B)
    (ha : ∀ t ∈ T, 0 < a t)
    (hb : ∀ t ∈ T, HasDerivAt b (bdot t) t)
    (hw : ∀ t ∈ T, HasDerivAt w (wdot t) t)
    (hZ : ∀ t ∈ T, HasDerivAt Z (Zdot t) t)
    (hColumns : ∀ t ∈ T,
      ‖b t‖ ≤ a t * B ^ 2 ∧ ‖w t‖ ≤ a t * B ^ 2)
    (hDet : ∀ t ∈ T,
      (a t) ^ 2 * B ^ 4 / 256 ≤ actualRealCramerDet (b t) (w t))
    (hPhysicalDeriv : ∀ᵐ r ∂volume, r ∈ Ι r0 B →
      ∀ t ∈ T,
        HasDerivAt
          (fun u => -actualHartreeLaplacianScaledKummerSource
            (a u) (ell u) (c u) (z u) r) (Fdot t r) t ∧
        HasDerivAt
          (fun u => actualMomentLockedScaledScaleSource (a u) (c u) r)
            (Sdot t r) t ∧
        HasDerivAt
          (fun u => actualMomentLockedScaledPhaseSource (a u) (c u) r)
            (Pdot t r) t)
    (hMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (originGreenSourceB K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
        (volume.restrict (Ι r0 B)))
    (hInt : IntervalIntegrable
      (originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume r0 B)
    (hDotMeas : AEStronglyMeasurable
      (originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSourceDot
          a ell c z b w Z Fdot Sdot Pdot s))
      (volume.restrict (Ι r0 B)))
    (hBound : ∀ᵐ r ∂volume, r ∈ Ι r0 B →
      ∀ t ∈ T,
        ‖originGreenSourceB K
          (actualHartreeTrueMovingAdjustedSourceDot
            a ell c z b w Z Fdot Sdot Pdot t) r‖ ≤ bound r)
    (hBoundInt : IntervalIntegrable bound volume r0 B) :
    HasDerivAt
      (fun t => originGreenCoeffB K r0
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t) B)
      (originGreenCoeffB K r0
        (actualHartreeTrueMovingAdjustedSourceDot
          a ell c z b w Z Fdot Sdot Pdot s) B) s := by
  apply actual_origin_Green_coeffB_fixed_lower_source_hasDerivAt
    K r0 B s
    (fun t => actualHartreeTrueMovingAdjustedSource a ell c z b w Z t)
    (fun t => actualHartreeTrueMovingAdjustedSourceDot
      a ell c z b w Z Fdot Sdot Pdot t)
    T bound hT hMeas hInt hDotMeas hBound hBoundInt
  filter_upwards [hPhysicalDeriv] with r hr
  intro hrmem t ht
  obtain ⟨hF, hS, hP⟩ := hr hrmem t ht
  have hCramer :=
    actual_Hartree_true_moving_adjusted_source_derivative
      a ell c z b w Z t r (a t) B (ha t ht) hB
      (bdot t) (wdot t) (Zdot t)
      (Fdot t r) (Sdot t r) (Pdot t r)
      (hb t ht) (hw t ht) (hZ t ht)
      (hColumns t ht).1 (hColumns t ht).2 (hDet t ht)
      hF hS hP
  obtain ⟨pbDot, pwDot, hpb, hpw, _hSpeed, hPhysical⟩ := hCramer
  have hpbEq :
      deriv (fun u =>
        (actualRealCramerCorrection (b u) (w u) (Z u)).1) t = pbDot :=
    hpb.deriv
  have hpwEq :
      deriv (fun u =>
        (actualRealCramerCorrection (b u) (w u) (Z u)).2) t = pwDot :=
    hpw.deriv
  simpa only [actualHartreeTrueMovingAdjustedSourceDot, hpbEq, hpwEq] using
    hPhysical

end HBL.TypeIIDynamicSelection
