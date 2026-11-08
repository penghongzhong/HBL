import HBL.TypeIIDynamicSelection.ActualHartreeSpectralCorrectedFourPieceThreeC1
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedFourPieceC1
import HBL.TypeIIDynamicSelection.ActualHartreeAdjustedKummerSourceContinuity
import Mathlib.Tactic

/-!
# Same genuine Hartree source and UNIQUE real speed: spectral-corrected three C¹ joins

The original three-dimensional quartic inverse-square Hartree source,
genuine two-channel Fredholm sources and original Cramer determinant
select a single unique compatible real velocity p. Use exactly this p
to correct the inner Fredholm forces and the Kummer forcing. For any
frozen spectral displacement d, the actual zero-left-jet matched Green
spectral correction preserves the original inner matching jet.

The right Kummer/repair join is reconstructed from the NEW corrected
upper value and derivative, while the exterior repair vanishes to first
order at 2aB. Thus the literal complete physical four-piece profile is
C¹ at L, aB and 2aB; no second independently chosen velocity or
postulated boundary traces appear.

This remains fixed-time C¹, not yet the full nonlocal moving Hartree PDE
positive residual increment or the derived Type-II blowup law.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_true_source_selected_spectral_four_piece_three_C1
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧
        ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < C ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
        L / a ≤ B → L < a * B →
      ∀ (Fp Fm : ℝ → ℝ)
        (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
        Continuous Fp → Continuous Fm →
      ∀ (Bz Az ell : ℝ), 0 ≤ Bz → 0 ≤ Az →
        0 < ell → ell ≤ 1 →
      ∀ (z : ℝ → ℂ), Measurable z →
        (∀ y : ℝ, 0 < y → ‖z y‖ ≤ Bz) →
        (∀ y : ℝ, 1 ≤ y → y * ‖z y‖ ≤ Az) →
        (∀ r ∈ Ioo (0 : ℝ) scale,
          ContinuousAt
            (fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x) r) →
      ∀ (d : ℂ),
        let F0 : ℝ → ℂ :=
          fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
        let Q : ℝ :=
          actualHartreePhysicalWeightedSourceConstant Bz Az *
            ell ^ (1 / 8 : ℝ)
        let N : ℝ :=
          innerWeightedNorm (7 / 4 : ℝ) Fp +
            innerWeightedNorm (7 / 4 : ℝ) Fm
        ∃ p : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F0 p.1 p.2 = 0 ∧
          (∀ q : ℝ × ℝ,
            actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
              Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
          (|p.1| + |p.2| ≤ (C / a) * (N + Q)) ∧
          let Gp := actualMomentLockedInnerPhaseSource L c
          let Gm := actualMomentLockedInnerScaleSource L c
          let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp
          let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp
          let Fpa := fun r => Fp r + p.2 * Gp r
          let Fma := fun r => Fm r + p.1 * Gm r
          let hpa := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp p.2
          let hma := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm p.1
          let Fo := fun r => F0 r +
            (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c r +
            (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c r
          let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
          let u := actualHartreeTwoChannelInner Fpa Fma hpa hma
          let w := actualHartreeMatchedSpectralCorrectedValue
            K (L / a) B Fo J.1 J.2 d
          let full := actualHartreeInnerKummerSpectralFourPiece
            K L a B Fpa Fma hpa hma Fo d
          HasDerivAt full (deriv u L) L ∧
            HasDerivAt full ((1 / a : ℝ) • deriv w B) (a * B) ∧
            HasDerivAt full (0 : ℂ) (2 * a * B) := by
  obtain ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, hPhysical⟩ :=
    actual_Hartree_true_source_unique_speed_full_four_piece_three_C1
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder hStrict
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss hF0Cont d
  dsimp only
  obtain ⟨p, hCompat, hUnique, hSpeed, _hOldThree⟩ :=
    hPhysical L c a hLp hLarge ha3 hSmall hOrder hStrict
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss hF0Cont
  refine ⟨p, hCompat, hUnique, hSpeed, ?_⟩
  dsimp only
  let F0 : ℝ → ℂ := fun x =>
    -actualHartreeLaplacianScaledKummerSource a ell c z x
  let Fo : ℝ → ℂ := fun x =>
    F0 x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
      (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp
  let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp
  let Fpa := fun x => Fp x + p.2 * Gp x
  let Fma := fun x => Fm x + p.1 * Gm x
  let hpa := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp p.2
  let hma := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm p.1
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hFoCont : ∀ r ∈ Ioo (0 : ℝ) scale,
      ContinuousAt Fo r := by
    intro r hr
    have hF : ContinuousAt F0 r := by
      simpa only [F0] using hF0Cont r hr
    simpa only [Fo, F0] using
      actual_Hartree_adjusted_Kummer_source_continuousAt
        a c r ha hr.1 F0 hF p
  have hThree :=
    actual_Hartree_spectral_inner_four_piece_three_C1_joins
      K L a hLp ha hOrder hBR hStrict
      Fpa Fma hpa hma Fo hFoCont d
  simpa only [Fo, F0, Gp, Gm, hgp, hgm,
    Fpa, Fma, hpa, hma] using hThree

end HBL.TypeIIDynamicSelection
