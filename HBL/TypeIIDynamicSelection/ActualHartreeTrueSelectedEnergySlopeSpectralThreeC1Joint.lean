import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedZeroLeftEnergySlope
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSelectedSpectralFourPieceThreeC1
import Mathlib.Tactic

/-!
# Same original Hartree speed: source-derived no-radius-loss radial energy AND corrected 3 C1 joins

One ORIGINAL quartic Riesz source F0 and original Fredholm data produce the
unique real compatible two-channel speed p.  At that SAME p, the actual
selected-adjusted source Fadj satisfies a genuine inverse-square estimate,
the original regular B-channel moment estimate, and hence an exact
no-hidden-left-radius Volterra radial-energy slope for the zero-left
spectral-repair source.  The genuine spectral-corrected FOUR-zone physical
field simultaneously matches at all three C1 interfaces.

The zero-left slope here is the algebraic Kummer Green slope; the
independent classical C1 assertion uses the actual source continuity
and existing Green derivative theorem. This is a source-specific
fixed-time bridge, not a positive time-power PDE residual nor a Type-II rate.
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

/-- One and the same uniquely selected real Cramer pair simultaneously
controls the original Hartree zero-left energy slope without shrinking
left-interface loss and all three spectral-corrected physical C1 joins. -/
theorem actual_Hartree_same_selected_Riesz_energy_slope_and_spectral_three_C1
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧
        ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon Cn Csel Csp Cjoin : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
      0 < Cn ∧ 0 < Csel ∧ 0 < Csp ∧ 0 < Cjoin ∧
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
        fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
      let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
        ell ^ (1 / 8 : ℝ)
      let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm
      let T : ℝ := ((8 / 3 : ℝ) * G * Q) * L ^ (-(3 / 8 : ℝ)) +
        (Csp * G * B * Csel) * (N + Q)
      ∃ (p : ℝ × ℝ) (Qa : ℝ),
        actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
          Fp Fm hp hm F0 p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
        0 ≤ Qa ∧ Qa ≤ Cn * (N + Q) ∧
        (∀ r ∈ Icc (L / a) B,
          let Fadj : ℝ → ℂ := fun x =>
            F0 x + (-(p.1 : ℂ)) *
              actualMomentLockedScaledScaleSource a c x +
              (-(p.2 : ℂ)) *
              actualMomentLockedScaledPhaseSource a c x
          ‖(r : ℂ) * actualOriginMatchedKummerSlope
              K (L / a) B Fadj 0 0 r‖ ≤
            (B + 1) * G * (1 + (D + 1) * G * B ^ 2) *
              (Cn * (N + Q)) +
            2 * (D + 1) * G * B ^ 2 * T) ∧
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
  obtain ⟨Le, ee, Cn, Csel, Csp,
    hLe, hee, heeOne, hCn, hCsel, hCsp, hEnergy⟩ :=
    actual_Hartree_true_source_unique_speed_zero_left_energy_slope
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨Lj, ej, Cjoin, hLj, hej, hejOne, hCjoin, hC1⟩ :=
    actual_Hartree_true_source_selected_spectral_four_piece_three_C1
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  let L0 := max Le Lj
  let epsilon := min ee ej
  have hL0 : 6 ≤ L0 := hLe.trans (le_max_left _ _)
  have heps : 0 < epsilon := lt_min hee hej
  have hepsOne : epsilon ≤ 1 := (min_le_left _ _).trans heeOne
  refine ⟨L0, epsilon, Cn, Csel, Csp, Cjoin,
    hL0, heps, hepsOne, hCn, hCsel, hCsp, hCjoin, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder hStrict
    Fp Fm hp hm hFp hFm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss hF0Cont d
  have hLargeE : Le ≤ L := (le_max_left _ _).trans hLarge
  have hLargeJ : Lj ≤ L := (le_max_right _ _).trans hLarge
  have hSmallE : a * |c| ≤ ee := hSmall.trans (min_le_left _ _)
  have hSmallJ : a * |c| ≤ ej := hSmall.trans (min_le_right _ _)
  dsimp only
  obtain ⟨p, Qa, hCompat, hUnique, hQa, hQaBudget, hSlope⟩ :=
    hEnergy L c a hLp hLargeE ha3 hSmallE hOrder
      Fp Fm hp hm hFp hFm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  obtain ⟨p2, hCompat2, _hUnique2, _hSpeed2, hThreeC1⟩ :=
    hC1 L c a hLp hLargeJ ha3 hSmallJ hOrder hStrict
      Fp Fm hp hm hFp hFm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss hF0Cont d
  have hp2 : p2 = p := hUnique p2 hCompat2
  subst p2
  refine ⟨p, Qa, hCompat, hUnique, hQa, hQaBudget, ?_, ?_⟩
  · exact hSlope
  · exact hThreeC1

end HBL.TypeIIDynamicSelection
