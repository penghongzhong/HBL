import HBL.TypeIIDynamicSelection.ActualHartreeTrueSelectedMatchedSpectralQuadratic
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSelectedSpectralFourPieceThreeC1
import Mathlib.Tactic

/-!
# One physical Hartree selector: source-derived quadratic spectral PDE and corrected C¹

The two source-faithful producers are joined by the UNIQUE real two-speed
compatibility solution of the original Hartree Fredholm equations. The
weighted initial matched profile is derived from the original nonlocal
quartic source, not postulated; the spectral Volterra correction preserves
its left data and has an exact weighted quadratic residual. In the same
physical profile and at the same velocity, the corrected upper jet is
used to rebuild the exterior repair, yielding the three literal C¹ joins.

This is a fixed-time bridge. It does not assume spectral time decay, moving
Kummer derivatives, nonlinear four-region residual improvement, finite
nonlinear recursion, or Type-II blowup rate.
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

/-- Literal 3D Hartree source gives one real compatible p for both the
no-independent-envelope quadratic spectral defect and all three actual
spectrally corrected physical C¹ interfaces. -/
theorem actual_Hartree_true_source_selected_spectral_quadratic_and_three_C1
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
        let H := (B * ((G * Cr * Cf * Cn + G * Cp + G ^ 2 * Cs * C) * (N + Q)) +
            G * ((((8 / 3 : ℝ) * G * Q) * L ^ (-(3 / 8 : ℝ))) +
              (Csp * G * B * Csel) * (N + Q))) +
          G ^ 2 * ((L / a) * ‖J.2‖ + (L / a + 1) * ‖J.1‖)
        ∀ (d : ℂ),
          (∀ (r : ℝ), r ∈ Icc (L / a) B →
            let v := actualHartreeMatchedSpectralCorrectedValue
              K (L / a) B Fadj J.1 J.2 d
            v (L / a) = J.1 ∧
              HasDerivAt v J.2 (L / a) ∧
              ‖(r : ℂ) *
                (deriv (deriv v) r + frozenFirstCoeff r * deriv v r +
                  (frozenZeroCoeff mu theta + d) * v r - Fadj r)‖ ≤
                (2 * G ^ 2 * (B - L / a)) * (‖d‖ ^ 2 * H)) ∧
          (let u := actualHartreeTwoChannelInner Fpa Fma hpa hma
           let w := actualHartreeMatchedSpectralCorrectedValue
             K (L / a) B Fadj J.1 J.2 d
           let full := actualHartreeInnerKummerSpectralFourPiece
             K L a B Fpa Fma hpa hma Fadj d
           HasDerivAt full (deriv u L) L ∧
             HasDerivAt full ((1 / a : ℝ) • deriv w B) (a * B) ∧
             HasDerivAt full (0 : ℂ) (2 * a * B)) := by
  obtain ⟨Lq, eq, C, Cs, Cn, Csel, Csp,
    hLq, heq, heqOne, hC, hCs, hCn, hCsel, hCsp, hQuadraticAll⟩ :=
    actual_Hartree_true_source_selected_matched_spectral_weighted_quadratic
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨Lj, ej, Cj, hLj, hej, hejOne, _hCj, hJoinedAll⟩ :=
    actual_Hartree_true_source_selected_spectral_four_piece_three_C1
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  let L0 := max Lq Lj
  let epsilon := min eq ej
  have hL0 : 6 ≤ L0 := hLq.trans (le_max_left _ _)
  have heps : 0 < epsilon := lt_min heq hej
  have hepsOne : epsilon ≤ 1 := (min_le_left _ _).trans heqOne
  refine ⟨L0, epsilon, C, Cs, Cn, Csel, Csp,
    hL0, heps, hepsOne, hC, hCs, hCn, hCsel, hCsp, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder hStrict
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss hF0Cont
  have hLargeQ : Lq ≤ L := (le_max_left _ _).trans hLarge
  have hLargeJ : Lj ≤ L := (le_max_right _ _).trans hLarge
  have hSmallQ : a * |c| ≤ eq := hSmall.trans (min_le_left _ _)
  have hSmallJ : a * |c| ≤ ej := hSmall.trans (min_le_right _ _)
  obtain ⟨p, hCompat, hUnique, hQuadratic⟩ :=
    hQuadraticAll L c a hLp hLargeQ ha3 hSmallQ hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss hF0Cont
  refine ⟨p, hCompat, hUnique, ?_⟩
  dsimp only
  intro d
  obtain ⟨q, hCompatQ, _hUniqueQ, _hSpeedQ, hThreeC1⟩ :=
    hJoinedAll L c a hLp hLargeJ ha3 hSmallJ hOrder hStrict
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss hF0Cont d
  have hqp : q = p := hUnique q hCompatQ
  subst q
  refine ⟨?_, ?_⟩
  · exact hQuadratic d
  · exact hThreeC1

end HBL.TypeIIDynamicSelection
