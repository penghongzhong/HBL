import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedFullOriginalGreenNoRadiusLoss
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedFromWeightedOriginalGreenCramer
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedFourPieceC1
import Mathlib.Tactic

/-!
# TRUE physical Hartree source -> one speed -> whole Cramer matched weighted field

This is the missing original-source producer for the first ACTUAL matched
Kummer field in the regularized weighted r|w| norm. Start from the real
inverse-square quartic Hartree Riesz source, original inner Fredholm
data and the uniquely compatible two-real-dimensional Cramer speed.
The accepted source-selected WHOLE original Green estimate controls
the inhomogeneous component without a hidden OriginBasisOn(r0) loss.

The exact compatibility equation eliminates the singular homogeneous
coefficient. The regular homogeneous Cramer component is bounded using
the original Fredholm left jet and exact origin-normalized Wronskian.
Therefore the full matched field obeys, at ALL intermediate radii,
 r|w_matched(r)| <= H_original_Green + G²(r0|DU|+(r0+1)|U|).
Every field and jet is constructed from the SAME selected speed.
The physical jet contribution is explicit, not a new arbitrary budget.

This does not assert a time-dependent selected orbit, positive nonlinear
time gain, the repaired spectral upper outgoing trace or Type-II rate.
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

theorem actual_Hartree_true_source_selected_whole_matched_weighted_no_radius_loss
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C Cs Cn Csel Csp : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
      0 < C ∧ 0 < Cs ∧ 0 < Cn ∧ 0 < Csel ∧ 0 < Csp ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
        L / a ≤ B →
      ∀ (Fp Fm : ℝ → ℝ)
        (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
        Continuous Fp → Continuous Fm →
      ∀ (Bz Az ell : ℝ), 0 ≤ Bz → 0 ≤ Az →
        0 < ell → ell ≤ 1 →
      ∀ (z : ℝ → ℂ), Measurable z →
        (∀ y : ℝ, 0 < y → ‖z y‖ ≤ Bz) →
        (∀ y : ℝ, 1 ≤ y → y * ‖z y‖ ≤ Az) →
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
        let Gp := actualMomentLockedInnerPhaseSource L c
        let Gm := actualMomentLockedInnerScaleSource L c
        let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp
        let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp
        let Fpa := fun r => Fp r + p.2 * Gp r
        let Fma := fun r => Fm r + p.1 * Gm r
        let hpa := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp p.2
        let hma := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm p.1
        let Fadj := fun r => F0 r +
          (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c r +
          (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c r
        let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
        ∀ r ∈ Icc (L / a) B,
          ‖(r : ℂ) * actualOriginMatchedKummerValue
              K (L / a) B Fadj J.1 J.2 r‖ ≤
            (B * ((G * Cr * Cf * Cn + G * Cp + G ^ 2 * Cs * C) * (N + Q)) +
              G * ((((8 / 3 : ℝ) * G * Q) * L ^ (-(3 / 8 : ℝ))) +
                (Csp * G * B * Csel) * (N + Q))) +
            G ^ 2 * ((L / a) * ‖J.2‖ + (L / a + 1) * ‖J.1‖) := by
  obtain ⟨L0, epsilon, C, Cs, Cn, Csel, Csp,
    hL0, heps, hepsOne, hC, hCs, hCn, hCsel, hCsp, hWhole⟩ :=
    actual_Hartree_true_source_selected_whole_original_Green_no_radius_loss
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, C, Cs, Cn, Csel, Csp,
    hL0, heps, hepsOne, hC, hCs, hCn, hCsel, hCsp, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss
  dsimp only
  obtain ⟨p, hCompat, hUnique, hGreen⟩ :=
    hWhole L c a hLp hLarge ha3 hSmall hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  refine ⟨p, hCompat, hUnique, ?_⟩
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
  let Fadj : ℝ → ℂ := fun x =>
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
  let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
  let Hg : ℝ :=
    B * ((G * Cr * Cf * Cn + G * Cp + G ^ 2 * Cs * C) * (N + Q)) +
      G * ((((8 / 3 : ℝ) * G * Q) * L ^ (-(3 / 8 : ℝ))) +
        (Csp * G * B * Csel) * (N + Q))
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hr0 : 0 < L / a := div_pos hLp ha
  have hCompatible :
      actualMomentLockedIntervalObstruction K (L / a) B Fadj J.1 J.2 = 0 := by
    change actualMomentLockedIntervalObstruction K (L / a) B Fadj J.1 J.2 = 0
      at hCompat
    exact hCompat
  have hWeightedGreen : ∀ x ∈ Icc (L / a) B,
      ‖(x : ℂ) * originGreenValue K (L / a) B Fadj x‖ ≤ Hg := by
    intro x hx
    simpa only [Hg, Fadj, F0, Q, N, Cr, Cp, Cf] using hGreen x hx
  intro r hr
  have hMatched :=
    actual_Hartree_matched_from_weighted_original_Green_and_Cramer
      K (L / a) B G Hg hr0 hOrder hBR hG hbound
      Fadj J.1 J.2 hCompatible hWeightedGreen r hr
  simpa only [Hg, Fadj, F0, Q, N, Cr, Cp, Cf, J,
    Gp, Gm, hgp, hgm, Fpa, Fma, hpa, hma] using hMatched

end HBL.TypeIIDynamicSelection
