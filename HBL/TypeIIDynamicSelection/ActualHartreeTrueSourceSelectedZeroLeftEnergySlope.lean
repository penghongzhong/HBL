import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftInverseSquareEnergySlopeCore
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedCorrectedNorm
import HBL.TypeIIDynamicSelection.ActualHartreeSelectedAdjustedRegularGreenAllRadii
import Mathlib.Tactic

/-!
# Same physical quartic Riesz source, unique real speed and zero-left energy slope

The authentic source F0=-a²*S_H(a*r), the same two real modulation
generators and the Fredholm inner-channel input produce their unique
compatible p. The correct inverse-square adjusted source Qa/r² is
obtained from the actual Hartree source-selected theorem; the correct
regular B-channel moment is independently obtained from the SAME p
by the original Riesz Green integral and the exact speed Cramer bound.
The exact zero-left Volterra cancellation then bounds r|u'_adj|
uniformly WITHOUT inserting a 1/r0 term, an unrelated norm, a
time-decay exponent or any Type-II rate as an assumption.

This is not yet the complete four-region true residual or finite PDE
iteration, and the algebraic Kummer slope requires a classical
differentiability bridge before it is identified with a spatial
derivative under merely measurable radiation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The true original Hartree PDE source and unique real Cramer speed supply
both inputs of the exact inverse-square zero-left radial-energy slope,
without any externally prescribed full-source or Green-moment budget. -/
theorem actual_Hartree_true_source_unique_speed_zero_left_energy_slope
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon Cn Csel Csp : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
      0 < Cn ∧ 0 < Csel ∧ 0 < Csp ∧
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
        fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
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
        ∀ r ∈ Icc (L / a) B,
          let Fadj : ℝ → ℂ := fun x =>
            F0 x + (-(p.1 : ℂ)) *
              actualMomentLockedScaledScaleSource a c x +
              (-(p.2 : ℂ)) *
              actualMomentLockedScaledPhaseSource a c x
          ‖(r : ℂ) * actualOriginMatchedKummerSlope
              K (L / a) B Fadj 0 0 r‖ ≤
            (B + 1) * G * (1 + (D + 1) * G * B ^ 2) *
              (Cn * (N + Q)) +
            2 * (D + 1) * G * B ^ 2 * T := by
  obtain ⟨L0n, epsn, Cn, hL0n, hepsn, hepsnOne, hCn, hNorm⟩ :=
    actual_Hartree_true_source_selected_corrected_inner_and_outer_norm
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨L0g, epsg, Csel, Csp,
    hL0g, hepsg, hepsgOne, hCsel, hCsp, hGreen⟩ :=
    actual_Hartree_true_source_selected_adjusted_regular_Green_all_radii
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  let L0 := max L0n L0g
  let epsilon := min epsn epsg
  have hL0 : 6 ≤ L0 :=
    hL0n.trans (le_max_left _ _)
  have heps : 0 < epsilon := lt_min hepsn hepsg
  have hepsOne : epsilon ≤ 1 := (min_le_left _ _).trans hepsnOne
  refine ⟨L0, epsilon, Cn, Csel, Csp,
    hL0, heps, hepsOne, hCn, hCsel, hCsp, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder
    Fp Fm hp hm hFp hFm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss
  dsimp only
  let F0 : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
    ell ^ (1 / 8 : ℝ)
  let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let T : ℝ := ((8 / 3 : ℝ) * G * Q) * L ^ (-(3 / 8 : ℝ)) +
    (Csp * G * B * Csel) * (N + Q)
  have hLargeN : L0n ≤ L := (le_max_left _ _).trans hLarge
  have hLargeG : L0g ≤ L := (le_max_right _ _).trans hLarge
  have hSmallN : a * |c| ≤ epsn :=
    hSmall.trans (min_le_left _ _)
  have hSmallG : a * |c| ≤ epsg :=
    hSmall.trans (min_le_right _ _)
  obtain ⟨p, Qa, hCompat, hUnique, hQa, hAdjusted, hBudget⟩ :=
    hNorm L c a hLp hLargeN ha3 hSmallN hOrder
      Fp Fm hp hm hFp hFm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  obtain ⟨pGreen, hCompatG, _hUniqueG, hBcoeffG⟩ :=
    hGreen L c a hLp hLargeG ha3 hSmallG hOrder
      Fp Fm hp hm hFp hFm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  have hpGreen : pGreen = p := hUnique pGreen hCompatG
  subst pGreen
  have hNonnegativeInner :
      0 ≤ innerWeightedNorm (7 / 4 : ℝ)
            (fun x => Fp x + p.2 * actualMomentLockedInnerPhaseSource L c x) +
          innerWeightedNorm (7 / 4 : ℝ)
            (fun x => Fm x + p.1 * actualMomentLockedInnerScaleSource L c x) :=
    add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hQaBudget : Qa ≤ Cn * (N + Q) := by
    dsimp only [N, Q] at hBudget ⊢
    linarith only [hBudget, hNonnegativeInner]
  refine ⟨p, Qa, ?_, ?_, hQa, hQaBudget, ?_⟩
  · simpa only [F0] using hCompat
  · intro q hq
    apply hUnique
    simpa only [F0] using hq
  · intro r hr
    let Fadj : ℝ → ℂ := fun x =>
      F0 x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
        (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
    have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
    have hr0 : 0 < L / a := div_pos hLp ha
    have hL : 1 ≤ L := by linarith
    have hN : 0 ≤ N :=
      add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
    have hQ : 0 ≤ Q := by
      dsimp [Q]
      exact mul_nonneg
        (actualHartreePhysicalWeightedSourceConstant_nonneg Bz Az hBz hAz)
        (Real.rpow_nonneg hell.le _)
    have hT : 0 ≤ T := by
      dsimp [T]
      have hLr : 0 ≤ L ^ (-(3 / 8 : ℝ)) :=
        Real.rpow_nonneg hLp.le _
      have hNQ : 0 ≤ N + Q := add_nonneg hN hQ
      positivity
    have hFI0 : IntervalIntegrable F0 volume (L / a) B :=
      (actual_Hartree_scaled_Kummer_source_intervalIntegrable
        Bz Az ell c a (L / a) B hBz hAz hell hellOne
        (by
          have hone : 1 ≤ a := (one_le_pow₀ hL).trans ha3
          have hc0 : a * |c| ≤ 1 := hSmallN.trans hepsnOne
          have hnonneg : 0 ≤ |c| := abs_nonneg c
          have hprod : 0 ≤ (a - 1) * |c| :=
            mul_nonneg (by linarith) hnonneg
          nlinarith only [hc0, hprod])
        ha hr0 hOrder z hz hSup hStrauss).neg
    have hFIspeed := actual_Hartree_moment_locked_scaled_speed_integrable_on
      a c (L / a) B ha hr0 hOrder
    have hFadjInt : IntervalIntegrable Fadj volume (L / a) B := by
      have hSum : IntervalIntegrable
          (fun x => ((-(p.1 : ℂ)) *
              actualMomentLockedScaledScaleSource a c x) +
            (-(p.2 : ℂ)) *
              actualMomentLockedScaledPhaseSource a c x) volume (L / a) B :=
        (hFIspeed.1.const_mul (-(p.1 : ℂ))).add
          (hFIspeed.2.const_mul (-(p.2 : ℂ)))
      simpa only [Fadj, add_assoc] using hFI0.add hSum
    have hFadjSquare (x : ℝ) (hx : x ∈ Icc (L / a) B) :
        ‖Fadj x‖ ≤ Qa / x ^ 2 := by
      have hRaw := hAdjusted x hx
      have hEq : Fadj x = F0 x -
          (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c x -
          (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c x := by
        dsimp [Fadj]
        ring
      rw [hEq]
      simpa only [F0] using hRaw
    have hBphysical (x : ℝ) (hx : x ∈ Icc (L / a) B) :
        ‖originGreenCoeffB K (L / a) Fadj x‖ ≤ T := by
      simpa only [T, Fadj, F0, N, Q] using hBcoeffG x hx
    have hCore :=
      actual_Hartree_zero_left_inverse_square_energy_slope_core
        K D G B (L / a) Qa T hD hG hr0 hOrder hBR hcoeff hbound
        hQa hT Fadj hFadjInt hFadjSquare hBphysical r hr
    let J : ℝ := 1 + (D + 1) * G * B ^ 2
    have hJ : 0 ≤ J := by dsimp [J]; positivity
    have hFactor : 0 ≤ (B + 1) * G * J := by positivity
    have hSize :
        (B + 1) * G * J * Qa +
          2 * (D + 1) * G * B ^ 2 * T ≤
        (B + 1) * G * J * (Cn * (N + Q)) +
          2 * (D + 1) * G * B ^ 2 * T :=
      add_le_add_right (mul_le_mul_of_nonneg_left hQaBudget hFactor) _
    have hFinal := hCore.trans hSize
    simpa only [Fadj, F0, J, N, Q, T] using hFinal

end HBL.TypeIIDynamicSelection
