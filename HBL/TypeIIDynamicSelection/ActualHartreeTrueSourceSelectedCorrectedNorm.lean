import HBL.TypeIIDynamicSelection.ActualHartreeMatchedExteriorSelected
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSpeedSelection
import Mathlib.Tactic

/-!
# Original Hartree source produces quantitatively bounded corrected Fredholm channels

The general real-Cramer source selection theorem produces not just a unique
compatible speed, but the actual weighted norms of BOTH corrected Fredholm
inner channels and the adjusted outer force envelope. Here the source is the
genuine nonlocal inverse-square quartic Hartree interaction
F0(r)=-a^2 S_H(ell,c,z)(a*r), rather than an arbitrary integrable packet.
The original spatial decay and integrability are derived directly from the
complete physical Riesz source. Neither the corrected inner source size
nor the adjusted outer source envelope is inserted as a premise.

This is a fixed moving-Kummer annulus estimate; time-dependent full-Hartree
residual improvement and the final Type-II rate are not claimed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_true_source_selected_corrected_inner_and_outer_norm
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
      ∃ (p : ℝ × ℝ) (Qa : ℝ),
        actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
          Fp Fm hp hm F0 p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
        0 ≤ Qa ∧
        (∀ r ∈ Icc (L / a) B,
          ‖F0 r - (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c r -
              (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c r‖ ≤
          Qa / r ^ 2) ∧
        innerWeightedNorm (7 / 4 : ℝ)
            (fun r => Fp r + p.2 * actualMomentLockedInnerPhaseSource L c r) +
          innerWeightedNorm (7 / 4 : ℝ)
            (fun r => Fm r + p.1 * actualMomentLockedInnerScaleSource L c r) +
            Qa ≤ C * (N + Q) := by
  obtain ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, hSelected⟩ :=
    actual_Hartree_selected_corrected_source_bounds_region
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss
  dsimp only
  let F0 : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let Q : ℝ :=
    actualHartreePhysicalWeightedSourceConstant Bz Az * ell ^ (1 / 8 : ℝ)
  let N : ℝ :=
    innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hLone : 1 ≤ L := by linarith
  have haOne : 1 ≤ a := (one_le_pow₀ hLone).trans ha3
  have hc : |c| ≤ 1 := by
    have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
    have hca : |c| ≤ a * |c| := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right haOne (abs_nonneg c))
    exact hca.trans hSmallOne
  have hr0 : 0 < L / a := div_pos hLp ha
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg
      (actualHartreePhysicalWeightedSourceConstant_nonneg Bz Az hBz hAz)
      (Real.rpow_nonneg hell.le _)
  have hFI : IntervalIntegrable F0 volume (L / a) B :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable
      Bz Az ell c a (L / a) B hBz hAz hell hellOne hc
      ha hr0 hOrder z hz hSup hStrauss).neg
  have hEnvelope : ∀ r ∈ Icc (L / a) B,
      ‖F0 r‖ ≤ Q / r ^ 2 := by
    intro r hr
    have hrp : 0 < r := hr0.trans_le hr.1
    have h :=
      actual_Hartree_scaled_Kummer_source_annulus_bound
        Bz Az ell c a r r hBz hAz hell hellOne hc
        ha hrp le_rfl z hz hSup hStrauss
    simpa only [F0, Q, norm_neg] using h
  obtain ⟨p, Qa, hCompat, hUnique, hQa, _hOrder, hAdj, hNorm⟩ :=
    hSelected L c a hLp hLarge ha3 hSmall
      Fp Fm hp hm hcp hcm F0 Q hQ hFI hEnvelope
  exact ⟨p, Qa, hCompat, hUnique, hQa, hAdj, hNorm⟩

end HBL.TypeIIDynamicSelection
