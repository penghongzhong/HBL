import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedCorrectedNorm
import HBL.TypeIIDynamicSelection.ActualHartreeFixedKummerOneStepSpectralGain
import Mathlib.Tactic

/-!
# §2.13: actual uniquely selected Hartree source -> one physical spectral step

Unlike a spectral correction theorem whose input is an arbitrary bound M
for an arbitrary Green forcing, this theorem starts with the genuine
inverse-square quartic nonlocal Hartree source and the SAME weighted
Fredholm two-channel data. The accepted physical nonlocal source theorem
CONSTRUCTS the UNIQUE compatible real modulation-speed pair p and the
corrected genuine outer source envelope Qa/r²; Qa is controlled directly
by the ORIGINAL inner weighted source norm and the physical ell^(1/8)
Hartree Riesz source budget.

We then apply the exact first original Wronskian Green spectral
correction, u1 = G_K0[(b(mu,theta)-b(mu0,theta0))*G_K0[Fadj]].
The frozen variable-parameter spectral error is quadratic in the
ACTUAL two-parameter displacement and controlled by the original
physical inputs, with NO arbitrarily supplied adjusted source M.

No positive order is claimed for moving cutoff transport, full
four-piece nonlocal Hartree PDE, the far-field or the finite recursion.
This is one nontrivial PHYSICAL Kummer-region spectral relative
step, not the complete paper §2.13. The Type-II rate is NOT a premise.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_original_selected_spectral_step_from_initial_source_norm
    {mu0 theta0 scale : ℝ}
    (K : OriginKummerPair mu0 theta0 scale)
    (D G B Ck : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hCk : 0 ≤ Ck)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu0 theta0‖ ≤ D)
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
      ∀ (mu theta : ℝ → ℝ) (t : ℝ),
      let r0 := L / a
      let F0 : ℝ → ℂ :=
        fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
      let Q := actualHartreePhysicalWeightedSourceConstant Bz Az *
        ell ^ (1 / 8 : ℝ)
      let N := innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm
      let delta := frozenZeroCoeff (mu t) (theta t) -
        frozenZeroCoeff mu0 theta0
      ∃ p : ℝ × ℝ,
        actualMomentLockedCoupledCompatibility K L c hLp a r0 B
          Fp Fm hp hm F0 p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a r0 B
            Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
        (∀ x ∈ Icc r0 B,
          let Fadj : ℝ → ℂ :=
            fun y => F0 y -
              (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c y -
              (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c y
          ‖actualHartreeOriginalSpectralCorrectedJetResidual
              K r0 B Fadj delta x - Fadj x‖ ≤
            (|mu t - mu0| + |theta t - theta0|) ^ 2 *
              (2 * Ck ^ 3 * (B - r0)) ^ 2 *
              (Csel * (N + Q) / r0 ^ 2)) := by
  obtain ⟨L0, epsilon, Csel, hL0, heps, hepsOne, hCsel, hPhysical⟩ :=
    actual_Hartree_true_source_selected_corrected_inner_and_outer_norm
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, Csel, hL0, heps, hepsOne, hCsel, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder hBasis
    Fp Fm hp hm hFp hFm Bz Az ell hBz hAz hell hellOne
    z hz hZBound hZStrauss mu theta t
  dsimp only
  let r0 : ℝ := L / a
  let F0 : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
    ell ^ (1 / 8 : ℝ)
  let N : ℝ :=
    innerWeightedNorm (7 / 4 : ℝ) Fp +
      innerWeightedNorm (7 / 4 : ℝ) Fm
  let delta : ℂ :=
    frozenZeroCoeff (mu t) (theta t) - frozenZeroCoeff mu0 theta0
  obtain ⟨p, Qa, hCompat, hUnique, hQa, hOuter, hAdjustedTotal⟩ :=
    hPhysical L c a hLp hLarge ha3 hSmall hOrder
      Fp Fm hp hm hFp hFm Bz Az ell hBz hAz hell hellOne
      z hz hZBound hZStrauss
  let Fadj : ℝ → ℂ := fun x =>
    F0 x - (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c x -
      (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c x
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hr0 : 0 < r0 := div_pos hLp ha
  have hNAdjusted : 0 ≤
      innerWeightedNorm (7 / 4 : ℝ)
        (fun x => Fp x + p.2 * actualMomentLockedInnerPhaseSource L c x) +
      innerWeightedNorm (7 / 4 : ℝ)
        (fun x => Fm x + p.1 * actualMomentLockedInnerScaleSource L c x) :=
    add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hQaOriginal : Qa ≤ Csel * (N + Q) := by
    dsimp only [N, Q] at hAdjustedTotal ⊢
    linarith only [hAdjustedTotal, hNAdjusted]
  have hM : 0 ≤ Qa / r0 ^ 2 :=
    div_nonneg hQa (sq_nonneg _)
  have hOriginalPoint : ∀ x ∈ Icc r0 B,
      ‖Fadj x‖ ≤ Qa / r0 ^ 2 := by
    intro x hx
    have hxPos : 0 < x := hr0.trans_le hx.1
    have hActual : ‖Fadj x‖ ≤ Qa / x ^ 2 := by
      simpa only [Fadj, F0, r0] using hOuter x hx
    have hSq : r0 ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ hr0.le hx.1 2
    have hDivide : Qa / x ^ 2 ≤ Qa / r0 ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hxPos) (sq_pos_of_pos hr0)).2
      exact mul_le_mul_of_nonneg_left hSq hQa
    exact hActual.trans hDivide
  have hSpec (x : ℝ) (hx : x ∈ Icc r0 B) :=
    actual_Hartree_original_Kummer_first_spectral_correction_quadratic_bound
      K r0 B Ck (Qa / r0 ^ 2)
      hCk hM hOrder hBasis Fadj hOriginalPoint delta x hx
  have hParam : ‖delta‖ ≤ |mu t - mu0| + |theta t - theta0| :=
    frozenZeroCoeff_difference_norm_le (mu t) (theta t) mu0 theta0
  have hParamSq :
      ‖delta‖ ^ 2 ≤
        (|mu t - mu0| + |theta t - theta0|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hParam 2
  have hSize :
      Qa / r0 ^ 2 ≤ Csel * (N + Q) / r0 ^ 2 :=
    div_le_div_of_nonneg_right hQaOriginal (sq_nonneg _)
  refine ⟨p, ?_, ?_, ?_⟩
  · simpa only [F0, r0] using hCompat
  · intro q hq
    apply hUnique
    simpa only [F0, r0] using hq
  · intro x hx
    have hResult := hSpec x hx
    have hNum :
        ‖delta‖ ^ 2 * (2 * Ck ^ 3 * (B - r0)) ^ 2 *
            (Qa / r0 ^ 2) ≤
          (|mu t - mu0| + |theta t - theta0|) ^ 2 *
            (2 * Ck ^ 3 * (B - r0)) ^ 2 *
            (Csel * (N + Q) / r0 ^ 2) := by
      have hPow := sq_nonneg (2 * Ck ^ 3 * (B - r0))
      have h1 := mul_le_mul_of_nonneg_right hParamSq hPow
      have h2 := mul_le_mul_of_nonneg_left hSize
        (mul_nonneg (sq_nonneg _) hPow)
      have hQaPos := hM
      nlinarith only [h1, h2, hQaPos, hParamSq, hSize, hPow]
    have hFinal := hResult.trans hNum
    simpa only [Fadj, F0, r0, delta, N, Q] using hFinal

end HBL.TypeIIDynamicSelection
