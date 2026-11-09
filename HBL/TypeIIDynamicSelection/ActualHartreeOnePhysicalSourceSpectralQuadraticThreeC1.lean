import HBL.TypeIIDynamicSelection.ActualHartreeTrueSelectedSpectralQuadraticThreeC1
import HBL.TypeIIDynamicSelection.ActualHartreeSinglePhysicalSourceTwoChannelSelection
import Mathlib.Tactic

/-!
# The same actual physical Hartree source through both corrected spectral interfaces

Both Fredholm channels are the literal real and imaginary parts of the
localized, radially conjugated original quartic nonlocal Hartree source
from the SAME radiation z generating the Kummer source. Weighted
membership is derived rather than separately assumed; continuity is
still an explicit regularity obligation. The real two-dimensional
compatibility selector is unique. Its actual corrected four-piece field
has three C¹ joins and the weighted quadratic frozen-Kummer residual.

This fixed-time theorem does not establish the moving parameter bounds,
the original full nonlocal PDE time-order gain or the final Type-II rate.
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

theorem actual_Hartree_one_physical_source_spectral_quadratic_and_three_C1
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
      ∀ (Bz Az ell c a : ℝ) (hell : 0 < ell),
        0 ≤ Bz → 0 ≤ Az → ell ≤ 1 →
        L0 ≤ actualHartreeSlowInnerRadius ell →
        (actualHartreeSlowInnerRadius ell) ^ 3 ≤ a →
        a * |c| ≤ epsilon →
        actualHartreeSlowInnerRadius ell / a ≤ B →
        actualHartreeSlowInnerRadius ell < a * B →
      ∀ (z : ℝ → ℂ), Measurable z →
        (∀ y : ℝ, 0 < y → ‖z y‖ ≤ Bz) →
        (∀ y : ℝ, 1 ≤ y → y * ‖z y‖ ≤ Az) →
        Continuous (actualHartreeTransmissionPlusSource ell c z) →
        Continuous (actualHartreeTransmissionMinusSource ell c z) →
        (∀ r ∈ Ioo (0 : ℝ) scale,
          ContinuousAt
            (fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x) r) →
      let L := actualHartreeSlowInnerRadius ell
      let Fp := actualHartreeTransmissionPlusSource ell c z
      let Fm := actualHartreeTransmissionMinusSource ell c z
      let hL : 0 < L := Real.rpow_pos_of_pos hell _
      ∃ (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
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
          actualMomentLockedCoupledCompatibility K L c hL a (L / a) B
            Fp Fm hp hm F0 p.1 p.2 = 0 ∧
          (∀ q : ℝ × ℝ,
            actualMomentLockedCoupledCompatibility K L c hL a (L / a) B
              Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
          let Gp := actualMomentLockedInnerPhaseSource L c
          let Gm := actualMomentLockedInnerScaleSource L c
          let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hL
          let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hL
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
  obtain ⟨L0, epsilon, C, Cs, Cn, Csel, Csp,
      hL0, heps, hepsOne, hC, hCs, hCn, hCsel, hCsp, hCombined⟩ :=
    actual_Hartree_true_source_selected_spectral_quadratic_and_three_C1
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, C, Cs, Cn, Csel, Csp,
    hL0, heps, hepsOne, hC, hCs, hCn, hCsel, hCsp, ?_⟩
  intro Bz Az ell c a hell hBz hAz hellOne hLarge ha3 hSmall hOrder hStrict
    z hz hSup hStrauss hcp hcm hFcont
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  let Fp := actualHartreeTransmissionPlusSource ell c z
  let Fm := actualHartreeTransmissionMinusSource ell c z
  have hL : 0 < L := Real.rpow_pos_of_pos hell _
  have hOne : 1 ≤ L := by linarith
  have ha : 0 < a := (pow_pos hL 3).trans_le ha3
  have haOne : 1 ≤ a := (one_le_pow₀ hOne).trans ha3
  have hc : |c| ≤ 1 := by
    have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
    have hca : |c| ≤ a * |c| := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right haOne (abs_nonneg c))
    exact hca.trans hSmallOne
  have hSource :=
    actual_Hartree_conjugated_slow_inner_one_sixteenth
      ell c Bz Az hell hellOne hc hBz hAz z hz hSup hStrauss
  have hPair :=
    actual_Hartree_one_complex_weighted_source_two_channels
      (7 / 4 : ℝ) _ hSource.1 hSource.2.1
  obtain ⟨p, hCompat, hUnique, hBoth⟩ :=
    hCombined L c a hL hLarge ha3 hSmall hOrder hStrict
      Fp Fm hPair.1 hPair.2 hcp hcm Bz Az ell hBz hAz
      hell hellOne z hz hSup hStrauss hFcont
  exact ⟨hPair.1, hPair.2, p, hCompat, hUnique, hBoth⟩

end HBL.TypeIIDynamicSelection
