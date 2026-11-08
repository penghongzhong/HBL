import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSpeedSelection
import HBL.TypeIIDynamicSelection.ActualHartreeInnerKummerRepairFourPieceC1
import HBL.TypeIIDynamicSelection.ActualHartreeAdjustedKummerSourceContinuity
import Mathlib.Tactic

/-!
# Same ORIGINAL Hartree source selects the full physical four-piece C1 field

A genuine three-dimensional inverse-square quartic Hartree Riesz source
F0(r)=-a^2 S_Hartree(a*r) uniquely selects a real compatibility
speed p, with a quantitative bound derived from the true source.
It produces the ACTUAL corrected two-channel Fredholm inner sources,
one corrected normalized Kummer forcing Fo, and the single physical
Fredholm-inner/Green/repair/zero four-piece field.

The already strict physical three-interface C1 certificate applies to
this SAME selected field, without independent Fredholm data,
boundary trace or compatible-speed hypothesis. The original
physical source is required to be continuous on the positive Kummer
annulus, a visible regularity premise; it is NOT deduced from
mere measurability of the radiation z.

This is a fixed physical time-slice bridge, not yet a dynamically
differentiable selected orbit, nor a full O(s^(-9/4)) Hartree residual.
The final Type-II rate is not prescribed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_true_source_unique_speed_full_four_piece_three_C1
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
      let F0 : ℝ → ℂ :=
        fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
      let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
        ell ^ (1 / 8 : ℝ)
      let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
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
        let full := actualHartreeInnerKummerFourPiece
          K L a B Fpa Fma hpa hma Fo
        let DU := actualOriginMatchedKummerSlope K (L / a) B Fo J.1 J.2 B
        HasDerivAt full (deriv u L) L ∧
        HasDerivAt full ((1 / a : ℝ) • DU) (a * B) ∧
        HasDerivAt full (0 : ℂ) (2 * a * B) := by
  obtain ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, hSelected⟩ :=
    actual_Hartree_true_nonlocal_source_selects_unique_real_speed
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder hStrict
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss hF0Cont
  dsimp only
  let F0 : ℝ → ℂ :=
    fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
  let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
    ell ^ (1 / 8 : ℝ)
  let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  obtain ⟨p, hCompat, hUnique, hSpeed⟩ :=
    hSelected L c a hLp hLarge ha3 hSmall hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  refine ⟨p, hCompat, hUnique, hSpeed, ?_⟩
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp
  let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp
  let Fpa := fun r => Fp r + p.2 * Gp r
  let Fma := fun r => Fm r + p.1 * Gm r
  let hpa := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp p.2
  let hma := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm p.1
  let Fo : ℝ → ℂ := fun r => F0 r +
    (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c r +
    (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c r
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hFoCont :
      ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt Fo r := by
    intro r hr
    exact actual_Hartree_adjusted_Kummer_source_continuousAt
      a c r ha hr.1 F0 (hF0Cont r hr) p
  have hJoined :=
    actual_Hartree_inner_Kummer_four_piece_three_C1_joins
      K L a hLp ha hOrder hBR hStrict
      Fpa Fma hpa hma Fo hFoCont
  simpa only [F0, Fpa, Fma, Fo] using hJoined

end HBL.TypeIIDynamicSelection
