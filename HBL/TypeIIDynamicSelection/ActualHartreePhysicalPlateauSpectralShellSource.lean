import HBL.TypeIIDynamicSelection.ActualHartreeBackwardSpectralFirstOrderShellGain
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedKummerPullback
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedPlateauSource
import Mathlib.Tactic

/-!
# True Hartree source to the original first-order spectral shell norm

This specializes the previously proved backward-shell value bound to the
ACTUAL quartic Hartree source, its two physical scale/phase speed channels
and the single Cramer-jet matched origin Kummer solution.  The original
Hartree plateau identity supplies the exact same-source PDE: it is NOT
postulated here.  Neither an arbitrary envelope nor a positive time
power is an input.  Global measurability of the matched pullback, which
is not obtained from local C2 regularity alone, remains explicit.

The estimate controls only the original first-order spectral source on
[L/2,L]; moving-time terms and nonlocal feedback outside the plateau
remain open, so this does not accept manuscript §2.13.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.Profile.Kummer HBL.L2Kernel

/-- The original spectral forcing of the physically matched Green
profile inherits its shell norm gain from the SAME quartic source.
The sole independent analytic input is global measurability. -/
theorem actual_Hartree_true_plateau_original_spectral_shell_source_norm
    (mu theta scale B ell c a db dw : ℝ)
    (K : OriginKummerPair mu theta scale) (z : ℝ → ℂ)
    (hp0 : InWeightedL2 (7 / 4 : ℝ)
      (actualHartreeTransmissionPlusSource ell c z))
    (hm0 : InWeightedL2 (7 / 4 : ℝ)
      (actualHartreeTransmissionMinusSource ell c z))
    (hcp0 : Continuous (actualHartreeTransmissionPlusSource ell c z))
    (hcm0 : Continuous (actualHartreeTransmissionMinusSource ell c z))
    (hLarge : 4 < actualHartreeSlowInnerRadius ell)
    (ha : 0 < a)
    (hCubic : actualHartreeSlowInnerRadius ell ^ 3 ≤ a)
    (hLB : actualHartreeSlowInnerRadius ell / a ≤ B)
    (hB : B < scale)
    (hSmall : 16 * (actualHartreeSlowInnerRadius ell / 2) ^ 2 *
      ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1)
    (hFo : ∀ r ∈ Ioo (0 : ℝ) scale,
      ContinuousAt
        (fun t => -actualHartreeLaplacianScaledKummerSource a ell c z t -
          (db : ℂ) * actualMomentLockedScaledScaleSource a c t -
          (dw : ℂ) * actualMomentLockedScaledPhaseSource a c t) r)
    (hMeas : ∀ U DU : ℂ,
      Measurable
        (actualOriginMatchedKummerPullback K a
          (actualHartreeSlowInnerRadius ell / a) B
          (fun t => -actualHartreeLaplacianScaledKummerSource a ell c z t -
            (db : ℂ) * actualMomentLockedScaledScaleSource a c t -
            (dw : ℂ) * actualMomentLockedScaledPhaseSource a c t) U DU))
    (delta : ℂ) :
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
      let v := actualOriginMatchedKummerPullback K a (L / a) B Fo J.1 J.2
      let N := innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm
      let A := actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
      let D := actualInnerShellValueConstant * N + 8 * R ^ 2 * A
      let E : ℝ → ℂ := fun y => ((a ^ 2)⁻¹ : ℝ) • (delta * v y)
      InWeightedL2 (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ∧
        innerWeightedNorm (7 / 4 : ℝ)
          (actualConjugatedShellMagnitude R E) ≤
            20 * (‖delta‖ * D) * R ^ (-(3 / 4 : ℝ)) := by
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  let R := L / 2
  let Fp0 := actualHartreeTransmissionPlusSource ell c z
  let Fm0 := actualHartreeTransmissionMinusSource ell c z
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  let Fp := fun r => Fp0 r + dw * Gp r
  let Fm := fun r => Fm0 r + db * Gm r
  let Fo : ℝ → ℂ := fun r =>
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
  have hleft : actualHartreeTwoChannelInner Fp Fm hp hm L = v L :=
    hJet.1.symm
  have hdleft : deriv (actualHartreeTwoChannelInner Fp Fm hp hm) L =
      deriv v L := hJet.2.2.1.symm
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
  have hCubicR : (2 * R) ^ 3 ≤ a := by rw [hTwoR]; exact hCubic
  have hOutput := actual_Hartree_backward_spectral_first_order_shell_source_gain
    mu theta a R L Fp Fm hp hm U v delta
    hcp hcm hU hSub ha hR hCubicR hSmall hAnchor
    hv hv2 (hMeas J.1 J.2) hleft hdleft hEquation
  exact hOutput

end HBL.TypeIIDynamicSelection
