import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedCorrectedNorm
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSourceUniformRegularJet
import Mathlib.Tactic

/-!
# One original nonlocal Hartree source -> unique real speed -> matched weighted first profile

The real two-channel Cramer selection uses the original nonlocal Hartree
source, not a generic forcing. Both the selected outer inverse-square
amplitude Qa and the corrected Fredholm left Cauchy jet are outputs of
that same source, inner pair, and unique real modulation-speed solution.
No independent jet, selected speed or adjusted outer-source envelope
is postulated.

The complete matched Kummer solution is bounded by the original
source and the actual corrected inner Cauchy coordinates. In particular
its regular homogeneous coefficient no longer uses a singular
unweighted Kummer basis constant. The source Green part still uses
OriginBasisOn, potentially nonuniform on moving shrinking annuli;
there is no claim of a time-positive nonlinear error or Type-II rate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_true_source_unique_speed_matched_weighted_from_Fredholm_jet
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B Ck : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hCk : 0 ≤ Ck)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon Csel : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < Csel ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
        (hOrder : L / a ≤ B) →
        (hBasis : OriginBasisOn K (L / a) B Ck) →
      ∀ (Fp Fm : ℝ → ℝ)
        (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
        Continuous Fp → Continuous Fm →
      ∀ (Bz Az ell : ℝ), 0 ≤ Bz → 0 ≤ Az →
        0 < ell → ell ≤ 1 →
      ∀ (z : ℝ → ℂ), Measurable z →
        (∀ y : ℝ, 0 < y → ‖z y‖ ≤ Bz) →
        (∀ y : ℝ, 1 ≤ y → y * ‖z y‖ ≤ Az) →
      let r0 := L / a
      let F0 : ℝ → ℂ :=
        fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
      let Q := actualHartreePhysicalWeightedSourceConstant Bz Az *
        ell ^ (1 / 8 : ℝ)
      let N := innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm
      ∃ (p : ℝ × ℝ) (Qa : ℝ),
        actualMomentLockedCoupledCompatibility K L c hLp a r0 B
          Fp Fm hp hm F0 p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a r0 B
            Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
        0 ≤ Qa ∧ Qa ≤ Csel * (N + Q) ∧
        (∀ r ∈ Icc r0 B,
          let Fadj : ℝ → ℂ :=
            fun y => F0 y -
              (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c y -
              (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c y
          let J := actualMomentLockedCanonicalInnerJet
            (fun y => Fp y + p.2 * actualMomentLockedInnerPhaseSource L c y)
            (fun y => Fm y + p.1 * actualMomentLockedInnerScaleSource L c y)
            (innerWeighted_add_smul_mem (7 / 4 : ℝ)
              Fp (actualMomentLockedInnerPhaseSource L c) hp
              (actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp) p.2)
            (innerWeighted_add_smul_mem (7 / 4 : ℝ)
              Fm (actualMomentLockedInnerScaleSource L c) hm
              (actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp) p.1)
            a r0
          ‖(r : ℂ) * actualOriginMatchedKummerValue K r0 B
            Fadj J.1 J.2 r‖ ≤
              B * ((2 * Ck ^ 2 * (B - r0)) * Qa) +
                G ^ 2 * (r0 * ‖J.2‖ + (r0 + 1) * ‖J.1‖)) := by
  obtain ⟨L0, epsilon, Csel, hL0, heps, hepsOne, hCsel, hPhysical⟩ :=
    actual_Hartree_true_source_selected_corrected_inner_and_outer_norm
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, Csel, hL0, heps, hepsOne, hCsel, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder hBasis
    Fp Fm hp hm hFp hFm Bz Az ell hBz hAz hell hellOne
    z hz hZBound hZStrauss
  dsimp only
  let r0 : ℝ := L / a
  let F0 : ℝ → ℂ :=
    fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
  let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
    ell ^ (1 / 8 : ℝ)
  let N : ℝ :=
    innerWeightedNorm (7 / 4 : ℝ) Fp +
      innerWeightedNorm (7 / 4 : ℝ) Fm
  obtain ⟨p, Qa, hCompat, hUnique, hQa, hOuter, hAdjustedTotal⟩ :=
    hPhysical L c a hLp hLarge ha3 hSmall hOrder
      Fp Fm hp hm hFp hFm Bz Az ell hBz hAz hell hellOne
      z hz hZBound hZStrauss
  let Fadj : ℝ → ℂ :=
    fun x => F0 x -
      (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c x -
      (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c x
  let J : ℂ × ℂ := actualMomentLockedCanonicalInnerJet
    (fun y => Fp y + p.2 * actualMomentLockedInnerPhaseSource L c y)
    (fun y => Fm y + p.1 * actualMomentLockedInnerScaleSource L c y)
    (innerWeighted_add_smul_mem (7 / 4 : ℝ)
      Fp (actualMomentLockedInnerPhaseSource L c) hp
      (actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp) p.2)
    (innerWeighted_add_smul_mem (7 / 4 : ℝ)
      Fm (actualMomentLockedInnerScaleSource L c) hm
      (actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp) p.1)
    a r0
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hr0 : 0 < r0 := div_pos hLp ha
  have hAdjustedNonneg : 0 ≤
      innerWeightedNorm (7 / 4 : ℝ)
        (fun y => Fp y + p.2 * actualMomentLockedInnerPhaseSource L c y) +
      innerWeightedNorm (7 / 4 : ℝ)
        (fun y => Fm y + p.1 * actualMomentLockedInnerScaleSource L c y) :=
    add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hQaOriginal : Qa ≤ Csel * (N + Q) := by
    dsimp only [N, Q] at hAdjustedTotal ⊢
    linarith only [hAdjustedTotal, hAdjustedNonneg]
  have hObstruction :
      actualMomentLockedIntervalObstruction K r0 B Fadj J.1 J.2 = 0 := by
    change actualMomentLockedIntervalObstruction K r0 B Fadj J.1 J.2 = 0 at hCompat
    exact hCompat
  have hOriginalPoint : ∀ x ∈ Icc r0 B,
      ‖Fadj x‖ ≤ Qa / x ^ 2 := by
    intro x hx
    simpa only [Fadj, F0, r0] using hOuter x hx
  have hGlobal : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧ ‖K.x x‖ ≤ G := by
    intro x hx
    exact ⟨(hbound x hx).1, (hbound x hx).2.1, (hbound x hx).2.2.1⟩
  refine ⟨p, Qa, ?_, ?_, hQa, hQaOriginal, ?_⟩
  · simpa only [F0, r0] using hCompat
  · intro q hq
    apply hUnique
    simpa only [F0, r0] using hq
  · intro r hr
    simpa only [Fadj, F0, r0, J] using
      actual_Hartree_matched_source_and_uniform_regular_jet_weighted
        K r0 B Ck G Qa hr0 hOrder hBR.le
          hCk hG hQa hBasis hGlobal Fadj hOriginalPoint
          J.1 J.2 hObstruction r hr

end HBL.TypeIIDynamicSelection
