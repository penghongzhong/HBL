import HBL.TypeIIDynamicSelection.ActualHartreeTwoSpeedRegularGreenAllRadii
import HBL.TypeIIDynamicSelection.ActualHartreeKummerRegularTailGain
import Mathlib.Tactic

/-!
# Original full adjusted physical Hartree regular Green coefficient

The adjusted source is the LITERAL sum of the original nonlocal quartic
Hartree Riesz source F0 and the original two real modulation generators.
The radius-dependent original regular Green coefficient is linear for
these three particular source terms: interval integrability is established
directly from the original physical-source and speed-generator theorems.

The uniform-in-radius physical source bound is O(L^(-3/8)), whereas the
two real speed source is O(a B (|p1|+|p2|)); no coarse Q/r^2 speed-envelope
or hidden 1/(L/a) basis bound is substituted. This theorem does NOT
assume an independent bound on the chosen speed or time-exponent.
Its next step is to substitute the unique real Fredholm-Cramer selector.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The genuine three-source adjusted regular Green channel is controlled
at every moving-annulus radius by its literal Hartree tail plus the
literal two real speed-generator moments. No source-norm assumption. -/
theorem actual_Hartree_adjusted_original_regular_Green_all_radii :
    ∃ Csp : ℝ, 0 < Csp ∧
      ∀ {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
        (D G L B a Bz Az ell c : ℝ),
        0 ≤ D → 0 ≤ G → 1 ≤ L → 0 < a →
        L / a ≤ B → B ≤ 1 → B < scale →
        a * |c| ≤ 1 → |c| ≤ 1 →
        (∀ x ∈ Icc 0 scale,
          ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D) →
        (∀ x ∈ Icc 0 scale,
          ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
          ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G) →
        0 ≤ Bz → 0 ≤ Az → 0 < ell → ell ≤ 1 →
        ∀ (z : ℝ → ℂ), Measurable z →
          (∀ y : ℝ, 0 < y → ‖z y‖ ≤ Bz) →
          (∀ y : ℝ, 1 ≤ y → y * ‖z y‖ ≤ Az) →
        ∀ (p : ℝ × ℝ) (r : ℝ) (_hr : r ∈ Icc (L / a) B),
          let F0 : ℝ → ℂ :=
            fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
          let Fsp : ℝ → ℂ :=
            fun x => (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
              (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
          let M : ℝ :=
            actualHartreePhysicalWeightedSourceConstant Bz Az *
              ell ^ (1 / 8 : ℝ)
          ‖originGreenCoeffB K (L / a) (fun x => F0 x + Fsp x) r‖ ≤
            (((8 / 3 : ℝ) * G * M) * L ^ (-(3 / 8 : ℝ))) +
              (Csp * G * a * B) * (|p.1| + |p.2|) := by
  obtain ⟨Csp, hCsp, hTwo⟩ :=
    actual_Hartree_two_real_speed_regular_Green_moment_all_radii
  refine ⟨Csp, hCsp, ?_⟩
  intro mu theta scale K D G L B a Bz Az ell c
    hD hG hL ha hOrder hBOne hBR hSmall hc
    hcoeff hbound hBz hAz hell hellOne z hz hSup hStrauss
    p r hr
  dsimp only
  let r0 : ℝ := L / a
  let F0 : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let Fsp : ℝ → ℂ :=
    fun x => (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
      (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
  let M : ℝ :=
    actualHartreePhysicalWeightedSourceConstant Bz Az * ell ^ (1 / 8 : ℝ)
  let Fo : ℝ → ℂ := fun x => F0 x + Fsp x
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hr0 : 0 < r0 := div_pos hLp ha
  have hBasis :
      OriginBasisOn K r0 r
        (G * (1 / r0 + 1 / r0 ^ 2) + r ^ 2 + 1) :=
    origin_kummer_annulus_bound K r0 r G hr0
      (hr.2.trans_lt hBR) hG hbound
  have hSourceInt0 : IntervalIntegrable F0 volume r0 r :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable
      Bz Az ell c a r0 r hBz hAz hell hellOne hc ha hr0
      (by simpa only [r0] using hr.1)
      z hz hSup hStrauss).neg
  have hSpeedInt :=
    actual_Hartree_moment_locked_scaled_speed_integrable_on
      a c r0 r ha hr0 (by simpa only [r0] using hr.1)
  have hSourceIntSp : IntervalIntegrable Fsp volume r0 r := by
    dsimp [Fsp]
    exact (hSpeedInt.1.const_mul (-(p.1 : ℂ))).add
      (hSpeedInt.2.const_mul (-(p.2 : ℂ)))
  have hGreenInt :=
    actual_origin_Green_source_integrability K hBasis hr.1
  have hInt0 :
      IntervalIntegrable (originGreenSourceB K F0) volume r0 r :=
    (hGreenInt F0 hSourceInt0).2
  have hIntSp :
      IntervalIntegrable (originGreenSourceB K Fsp) volume r0 r :=
    (hGreenInt Fsp hSourceIntSp).2
  have hSourceAdd :
      originGreenSourceB K Fo =
        (fun x => originGreenSourceB K F0 x + originGreenSourceB K Fsp x) := by
    funext x
    dsimp [Fo, originGreenSourceB]
    ring
  have hCoeffAdd :
      originGreenCoeffB K r0 Fo r =
        originGreenCoeffB K r0 F0 r +
          originGreenCoeffB K r0 Fsp r := by
    unfold originGreenCoeffB
    rw [hSourceAdd, intervalIntegral.integral_add hInt0 hIntSp]
  have hOriginal :=
    actual_Hartree_scaled_Kummer_both_Green_coefficients_uniform
      K D G L B a Bz Az ell c
      hD hG hL ha hOrder hBR hcoeff hbound
      hBz hAz hell hellOne hc z hz hSup hStrauss r hr
  have hOrigB :
      ‖originGreenCoeffB K r0 F0 r‖ ≤
        ((8 / 3 : ℝ) * G * M) * L ^ (-(3 / 8 : ℝ)) := by
    simpa only [F0, r0, M] using hOriginal.2
  have hSp :
      ‖originGreenCoeffB K r0 Fsp r‖ ≤
        (Csp * G * a * B) * (|p.1| + |p.2|) := by
    simpa only [Fsp, r0] using
      (hTwo K G L c a B hG hL ha hBOne hBR hSmall hbound p r hr)
  have hTotal :
      ‖originGreenCoeffB K r0 Fo r‖ ≤
        ((8 / 3 : ℝ) * G * M) * L ^ (-(3 / 8 : ℝ)) +
          (Csp * G * a * B) * (|p.1| + |p.2|) := by
    rw [hCoeffAdd]
    exact (norm_add_le _ _).trans (add_le_add hOrigB hSp)
  simpa only [Fo, F0, Fsp, M, r0] using hTotal

end HBL.TypeIIDynamicSelection
