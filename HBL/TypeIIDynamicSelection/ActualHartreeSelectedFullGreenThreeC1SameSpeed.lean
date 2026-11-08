import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedFullOriginalGreenNoRadiusLoss
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedFourPieceC1
import Mathlib.Tactic

/-!
# One selected nonlocal Hartree source: whole weighted Green and all three C¹ joins

The independently established full original Green estimate and the genuine
Fredholm/Green/repair/zero C¹ matching certificate are identified at the
SAME uniquely selected real two-dimensional speed. Their matching is not
achieved by postulating independent speeds or an annular forcing envelope.

This is a fixed physical time-slice statement. It requires the explicitly
visible source continuity needed to differentiate its physical Green integral,
but does not postulate a time order or an II-type blowup law. The moving
Kummer basis, spectral outgoing repair, four-region dynamical Hartree residual
and nonlinear finite recursion are not consequences of this lemma.
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

/-- The original three-dimensional Hartree source simultaneously generates
one unique real compatible speed, a whole Green field estimate at *every*
intermediate radius without a hidden inverse left-radius basis constant,
and the literal three C¹ joins for the corrected four-piece field. -/
theorem actual_Hartree_same_selected_speed_whole_Green_and_three_C1
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧
        ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C Cs Cn Csel Csp Cjoin : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
      0 < C ∧ 0 < Cs ∧ 0 < Cn ∧ 0 < Csel ∧
      0 < Csp ∧ 0 < Cjoin ∧
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
      let F0 : ℝ → ℂ :=
        fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
      let Q : ℝ :=
        actualHartreePhysicalWeightedSourceConstant Bz Az * ell ^ (1 / 8 : ℝ)
      let N : ℝ :=
        innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm
      let Cr : ℝ := 1 + (D + 1) * G * (B ^ 2 + 2)
      let Cp : ℝ := 1 + (D + 1) * G * B ^ 2
      let Cf : ℝ :=
        actualInnerShellValueConstant + actualInnerShellDerivativeConstant
      ∃ p : ℝ × ℝ,
        actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
          Fp Fm hp hm F0 p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
        (∀ r ∈ Icc (L / a) B,
          let Fadj : ℝ → ℂ := fun x =>
            F0 x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
              (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
          ‖(r : ℂ) * originGreenValue K (L / a) B Fadj r‖ ≤
            B * ((G * Cr * Cf * Cn + G * Cp + G ^ 2 * Cs * C) * (N + Q)) +
              G * ((((8 / 3 : ℝ) * G * Q) * L ^ (-(3 / 8 : ℝ))) +
                (Csp * G * B * Csel) * (N + Q))) ∧
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
        let full := actualHartreeInnerKummerFourPiece
          K L a B Fpa Fma hpa hma Fo
        let DU := actualOriginMatchedKummerSlope K (L / a) B Fo J.1 J.2 B
        HasDerivAt full (deriv u L) L ∧
        HasDerivAt full ((1 / a : ℝ) • DU) (a * B) ∧
        HasDerivAt full (0 : ℂ) (2 * a * B) := by
  obtain ⟨Lw, ew, C, Cs, Cn, Csel, Csp,
    hLw, hew, hewOne, hC, hCs, hCn, hCsel, hCsp, hWhole⟩ :=
    actual_Hartree_true_source_selected_whole_original_Green_no_radius_loss
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨Lj, ej, Cjoin, hLj, hej, hejOne, hCjoin, hJoined⟩ :=
    actual_Hartree_true_source_unique_speed_full_four_piece_three_C1
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  let L0 := max Lw Lj
  let epsilon := min ew ej
  have hL0 : 6 ≤ L0 := hLw.trans (le_max_left _ _)
  have heps : 0 < epsilon := lt_min hew hej
  have hepsOne : epsilon ≤ 1 := (min_le_left _ _).trans hewOne
  refine ⟨L0, epsilon, C, Cs, Cn, Csel, Csp, Cjoin,
    hL0, heps, hepsOne, hC, hCs, hCn, hCsel, hCsp, hCjoin, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder hStrict
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss hF0Cont
  have hLargeW : Lw ≤ L := (le_max_left _ _).trans hLarge
  have hLargeJ : Lj ≤ L := (le_max_right _ _).trans hLarge
  have hSmallW : a * |c| ≤ ew := hSmall.trans (min_le_left _ _)
  have hSmallJ : a * |c| ≤ ej := hSmall.trans (min_le_right _ _)
  obtain ⟨p, hCompat, hUnique, hWeighted⟩ :=
    hWhole L c a hLp hLargeW ha3 hSmallW hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  obtain ⟨q, hCompatQ, _hUniqueQ, _hSpeedQ, hThreeC1⟩ :=
    hJoined L c a hLp hLargeJ ha3 hSmallJ hOrder hStrict
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss hF0Cont
  have hqp : q = p := hUnique q hCompatQ
  subst q
  refine ⟨p, hCompat, hUnique, ?_, ?_⟩
  · exact hWeighted
  · exact hThreeC1

end HBL.TypeIIDynamicSelection
