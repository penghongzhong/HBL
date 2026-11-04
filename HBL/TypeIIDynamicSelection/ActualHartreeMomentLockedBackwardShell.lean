import HBL.TypeIIDynamicSelection.ActualHartreeMatchedShellWeightedGain
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedKummerPullback
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedPlateauSource
import Mathlib.Tactic

/-!
# The actual moment-locked backward overlap in the original source norm

The inner sources are the real and imaginary parts of the original
localized Hartree interaction, with the two genuine speed corrections
added through the same fixed Fredholm inverses.  The exterior field is
the explicit origin Green continuation matched to that actual inner
Cauchy jet at L.  Its original source is unchanged below L.

The overlap [L/2,L] lies wholly inside the original source plateau.
Consequently the same-source equation, local C2 regularity and zero
interface jet are conclusions of the construction.  They are not
inputs to the final weighted shell estimate.  The upper trace remains
the same complete compatibility obstruction as in the speed selection.

This is a frozen linear overlap estimate. It does not claim a full
nonlinear residual improvement or a finite-profile construction.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.Profile.Kummer

/-- The actual physical sources and explicitly matched exterior profile
give a relative shell estimate in the original fixed-inverse source norm.
The unchanged upper trace is returned for the same constructed profile. -/
theorem actual_Hartree_moment_locked_backward_shell_weighted_gain :
    ∃ C : ℝ, 0 < C ∧
      ∀ (mu theta scale B ell c a db dw : ℝ)
        (K : OriginKummerPair mu theta scale) (z : ℝ → ℂ)
        (_hp0 : InWeightedL2 (7 / 4 : ℝ)
          (actualHartreeTransmissionPlusSource ell c z))
        (_hm0 : InWeightedL2 (7 / 4 : ℝ)
          (actualHartreeTransmissionMinusSource ell c z)),
        Continuous (actualHartreeTransmissionPlusSource ell c z) →
        Continuous (actualHartreeTransmissionMinusSource ell c z) →
        4 < actualHartreeSlowInnerRadius ell → 0 < a →
        actualHartreeSlowInnerRadius ell / a ≤ B → B < scale →
        16 * (actualHartreeSlowInnerRadius ell / 2) ^ 2 *
          ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1 →
        (∀ r ∈ Ioo 0 scale, ContinuousAt (fun t =>
          -actualHartreeLaplacianScaledKummerSource a ell c z t -
            (db : ℂ) * actualMomentLockedScaledScaleSource a c t -
            (dw : ℂ) * actualMomentLockedScaledPhaseSource a c t) r) →
        let L := actualHartreeSlowInnerRadius ell
        let R := L / 2
        let Fp := fun r => actualHartreeTransmissionPlusSource ell c z r +
          dw * actualMomentLockedInnerPhaseSource L c r
        let Fm := fun r => actualHartreeTransmissionMinusSource ell c z r +
          db * actualMomentLockedInnerScaleSource L c r
        let Fo := fun r =>
          -actualHartreeLaplacianScaledKummerSource a ell c z r -
            (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
            (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
        ∃ (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
          (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
        let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
        let w := actualOriginMatchedKummerValue K (L / a) B Fo J.1 J.2
        let v := actualOriginMatchedKummerPullback K a (L / a) B Fo J.1 J.2
        let d := fun r => actualHartreeTwoChannelInner Fp Fm hp hm r - v r
        let E := actualMatchedKummerShellError mu theta a R d
        InWeightedL2 (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ∧
        innerWeightedNorm (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ≤
          20 * C *
            (actualInnerShellEquationConstant * R ^ (-(3 / 4 : ℝ)) +
              actualInnerShellKummerConstant mu theta * R ^ (13 / 4 : ℝ) / a ^ 2) *
            (innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm) ∧
        actualOriginOutgoingTrace K B (w B) (deriv w B) =
          actualMomentLockedIntervalObstruction K (L / a) B Fo J.1 J.2 := by
  obtain ⟨C, hC, hWeighted⟩ := actual_Hartree_two_channel_matched_shell_weighted_gain
  refine ⟨C, hC, ?_⟩
  intro mu theta scale B ell c a db dw K z hp0 hm0 hcp0 hcm0 hLarge ha hLB hB hsmall hFo
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  let R := L / 2
  let Fp0 := actualHartreeTransmissionPlusSource ell c z
  let Fm0 := actualHartreeTransmissionMinusSource ell c z
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  let Fp := fun r => Fp0 r + dw * Gp r
  let Fm := fun r => Fm0 r + db * Gm r
  let Fo := fun r =>
    -actualHartreeLaplacianScaledKummerSource a ell c z r -
      (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
      (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
  have hL : 0 < L := by dsimp [L]; linarith
  have hgp : InWeightedL2 (7 / 4 : ℝ) Gp :=
    actual_Hartree_moment_locked_inner_phase_source_weighted L c hL
  have hgm : InWeightedL2 (7 / 4 : ℝ) Gm :=
    actual_Hartree_moment_locked_inner_scale_source_weighted L c hL
  have hp : InWeightedL2 (7 / 4 : ℝ) Fp :=
    innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp0 Gp hp0 hgp dw
  have hm : InWeightedL2 (7 / 4 : ℝ) Fm :=
    innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm0 Gm hm0 hgm db
  have hSpeedCont := actual_Hartree_moment_locked_inner_sources_continuous L c
  have hcp : Continuous Fp := hcp0.add (continuous_const.mul hSpeedCont.2)
  have hcm : Continuous Fm := hcm0.add (continuous_const.mul hSpeedCont.1)
  refine ⟨hp, hm, ?_⟩
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let w := actualOriginMatchedKummerValue K (L / a) B Fo J.1 J.2
  let v := actualOriginMatchedKummerPullback K a (L / a) B Fo J.1 J.2
  let U : Set ℝ := Ioo 0 (a * scale)
  have hR : 2 < R := by dsimp [R, L]; linarith
  have hRpos : 0 < R := by linarith
  have hTwoR : 2 * R = L := by dsimp [R]; ring
  have hLupper : L < a * scale := by
    have h := (div_lt_iff₀ ha).1 (hLB.trans_lt hB)
    simpa only [mul_comm] using h
  have hU : IsOpen U := isOpen_Ioo
  have hSub : Icc R (2 * R) ⊆ U := by
    intro x hx
    have hxL : x ≤ L := hx.2.trans_eq hTwoR
    exact ⟨hRpos.trans_le hx.1, hxL.trans_lt hLupper⟩
  have hAnchor : L ∈ Icc R (2 * R) := by
    refine ⟨?_, ?_⟩
    · dsimp [R]
      linarith
    · rw [hTwoR]
  have hClass := actual_Hartree_matched_Kummer_pullback_classical K a ha
    (div_pos hL ha) hLB hB Fo hFo J.1 J.2
  have hv : ∀ x ∈ U, DifferentiableAt ℝ v x :=
    fun x hx => (hClass x hx).1.differentiableAt
  have hv2 : ∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv v) x :=
    fun x hx => (hClass x (hSub hx)).2.1
  have hJet := actual_Hartree_moment_locked_pullback_actual_inner_jet K L a hL ha
    hLB hB Fp Fm hp hm Fo hFo
  have hleft : actualHartreeTwoChannelInner Fp Fm hp hm L = v L := hJet.1.symm
  have hdleft : deriv (actualHartreeTwoChannelInner Fp Fm hp hm) L = deriv v L :=
    hJet.2.2.1.symm
  have hEquation : ∀ x ∈ Icc R (2 * R),
      actualMatchedScaledKummerApply mu theta a v x =
        -actualHartreeTwoChannelPhysicalSource Fp Fm x := by
    intro x hx
    rw [(hClass x (hSub hx)).2.2]
    have hPlateau : ((a ^ 2)⁻¹ : ℝ) • Fo (x / a) +
        actualHartreeTwoChannelPhysicalSource Fp Fm x = 0 :=
      actual_Hartree_moment_locked_plateau_scaled_source a ell c z x db dw ha hL
        (hSub hx).1 (hx.2.trans_eq hTwoR)
    exact eq_neg_of_add_eq_zero_left hPlateau
  have hw := hWeighted mu theta a R L Fp Fm hp hm U v
    hcp hcm hU hSub ha hR hsmall hAnchor hv hv2 hleft hdleft hEquation
  refine ⟨hw.1, hw.2.2, ?_⟩
  exact actual_origin_matched_Kummer_actual_upper_trace K
    (div_pos hL ha) hLB hB Fo hFo J.1 J.2

end HBL.TypeIIDynamicSelection
