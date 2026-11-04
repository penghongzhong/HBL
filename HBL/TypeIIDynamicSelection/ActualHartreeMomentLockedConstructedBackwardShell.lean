import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedBackwardShell
import HBL.TypeIIDynamicSelection.ActualHartreeBackwardShellRegion
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer

/-!
Constructed compatibility cancellation and the actual backward overlap
are combined for the SAME physical Hartree source and the SAME normalized
Fredholm responses.  The basis, real speed increments, inner weighted
membership, and outer source integrability are all constructed.

The overlap is [L/2,L], inside the plateau of the original source cutoff.
Its error is measured in the original 7/4 source norm with a genuine
(L/2)^(-3/4) factor.  The norm on the right is explicitly that of the
ADJUSTED two-channel input.  No estimate replacing it by the base input
is asserted.  The finite upper trace uses the actual derivative of the
same exterior profile; it is not an infinity radiation condition.

Physical source regularity is retained as an explicit input.  This frozen
linear construction does not assert a nonlinear residual recursion.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.Profile.Kummer

/-- The actual adjusted physical profiles, their backward overlap error,
its original weighted norm, and the finite upper trace of the same profile.
The displayed gain is a conclusion of the terminal construction below. -/
def ActualMomentLockedPhysicalBackwardShellConclusion
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B C ell c a : ℝ) (z : ℝ → ℂ) (db dw : ℝ) : Prop :=
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
        C * (actualInnerShellEquationConstant + actualInnerShellKummerConstant mu theta) *
          R ^ (-(3 / 4 : ℝ)) *
          (innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm) ∧
      actualOriginOutgoingTrace K B (w B) (deriv w B) = 0

/-- Construct the unique real compatibility correction and its actual
backward overlap for the original physical source.  The cubic scale
separation also supplies the weak Kummer absorption and the negative
radius power.  No matching, matrix invertibility, source membership,
outer source integrability, or shell gain is an input. -/
theorem actual_Hartree_moment_locked_constructed_backward_shell
    (mu theta : ℝ) :
    ∃ (K : OriginKummerPair mu theta 1) (B L0 epsilon C : ℝ),
      0 < B ∧ B < 1 ∧ 6 ≤ L0 ∧ 0 < epsilon ∧ 0 < C ∧
      ∀ (B0 A0 ell c a : ℝ) (z : ℝ → ℂ) (hell : 0 < ell),
        0 ≤ B0 → 0 ≤ A0 → ell ≤ 1 → |c| ≤ 1 →
        L0 ≤ actualHartreeSlowInnerRadius ell →
        actualHartreeSlowInnerRadius ell ^ 3 ≤ a → a * |c| ≤ epsilon →
        Measurable z →
        (∀ r : ℝ, 0 < r → ‖z r‖ ≤ B0) →
        (∀ r : ℝ, 1 ≤ r → r * ‖z r‖ ≤ A0) →
        Continuous (actualHartreeTransmissionPlusSource ell c z) →
        Continuous (actualHartreeTransmissionMinusSource ell c z) →
        (∀ db dw r : ℝ, r ∈ Ioo (0 : ℝ) 1 →
          ContinuousAt (fun t =>
            -actualHartreeLaplacianScaledKummerSource a ell c z t -
              (db : ℂ) * actualMomentLockedScaledScaleSource a c t -
              (dw : ℂ) * actualMomentLockedScaledPhaseSource a c t) r) →
        let L := actualHartreeSlowInnerRadius ell
        let hL : 0 < L := Real.rpow_pos_of_pos hell _
        let Fp0 := actualHartreeTransmissionPlusSource ell c z
        let Fm0 := actualHartreeTransmissionMinusSource ell c z
        let F0 := fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
        0 < L / a ∧ L / a < B ∧
        ∃ (hp0 : InWeightedL2 (7 / 4 : ℝ) Fp0)
          (hm0 : InWeightedL2 (7 / 4 : ℝ) Fm0) (p : ℝ × ℝ),
          ActualMomentLockedMatchedKummerCertificate K L c hL a (L / a) B
            Fp0 Fm0 hp0 hm0 F0 p.1 p.2 ∧
          (∀ q : ℝ × ℝ,
            ActualMomentLockedMatchedKummerCertificate K L c hL a (L / a) B
              Fp0 Fm0 hp0 hm0 F0 q.1 q.2 → q = p) ∧
          ActualMomentLockedPhysicalBackwardShellConclusion K B C ell c a z p.1 p.2 := by
  obtain ⟨K, B, Lold, epsilon, hB, hBOne, _hLold, hepsilon, hConstruct⟩ :=
    actual_Hartree_moment_locked_constructed_matched_Kummer mu theta
  obtain ⟨Cshell, hCshell, hBackward⟩ :=
    actual_Hartree_moment_locked_backward_shell_weighted_gain
  let L0 : ℝ := max Lold (max 6 (4 * (1 + ‖frozenZeroCoeff mu theta‖)))
  have hL0six : 6 ≤ L0 :=
    (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨K, B, L0, epsilon, 20 * Cshell, hB, hBOne, hL0six,
    hepsilon, by positivity, ?_⟩
  intro B0 A0 ell c a z hell hB0 hA0 hellOne hc hLarge ha3 hSmall
    hz hSup hStrauss hcp0 hcm0 hOuterCont
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  let R := L / 2
  let Fp0 := actualHartreeTransmissionPlusSource ell c z
  let Fm0 := actualHartreeTransmissionMinusSource ell c z
  let F0 : ℝ → ℂ := fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
  have hL : 0 < L := Real.rpow_pos_of_pos hell _
  have hOld : Lold ≤ L := (le_max_left _ _).trans hLarge
  have hExtra : max 6 (4 * (1 + ‖frozenZeroCoeff mu theta‖)) ≤ L :=
    (le_max_right _ _).trans hLarge
  have hLsix : 6 ≤ L := (le_max_left _ _).trans hExtra
  have hLfour : 4 < L := by linarith
  have ha : 0 < a := (pow_pos hL 3).trans_le ha3
  have hRegion := hConstruct L c a hL hOld ha3 hc hSmall
  have hr0 : 0 < L / a := hRegion.1
  have hLB : L / a < B := hRegion.2.1
  have hWeak := actual_Hartree_backward_shell_weak_budget mu theta L a hExtra ha3
  have hSource := actual_Hartree_conjugated_slow_inner_one_sixteenth
    ell c B0 A0 hell hellOne hc hB0 hA0 z hz hSup hStrauss
  have hPair := actual_Hartree_one_complex_weighted_source_two_channels
    (7 / 4 : ℝ) _ hSource.1 hSource.2.1
  have hp0 : InWeightedL2 (7 / 4 : ℝ) Fp0 := hPair.1
  have hm0 : InWeightedL2 (7 / 4 : ℝ) Fm0 := hPair.2
  have hF0 : IntervalIntegrable F0 volume (L / a) B :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable B0 A0 ell c a
      (L / a) B hB0 hA0 hell hellOne hc ha hr0 hLB.le z hz hSup hStrauss).neg
  obtain ⟨p, hpCert, hpUnique⟩ := hRegion.2.2 Fp0 Fm0 hp0 hm0 F0 hF0
  refine ⟨hr0, hLB, hp0, hm0, p, hpCert, hpUnique, ?_⟩
  let Fp := fun r => Fp0 r + p.2 * actualMomentLockedInnerPhaseSource L c r
  let Fm := fun r => Fm0 r + p.1 * actualMomentLockedInnerScaleSource L c r
  let Fo := fun r =>
    -actualHartreeLaplacianScaledKummerSource a ell c z r -
      (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c r -
      (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c r
  have hFo : ∀ r ∈ Ioo (0 : ℝ) 1, ContinuousAt Fo r := hOuterCont p.1 p.2
  obtain ⟨hp, hm, hShell⟩ := hBackward mu theta 1 B ell c a p.1 p.2 K z hp0 hm0
    hcp0 hcm0 hLfour ha hLB.le hBOne hWeak.2 hFo
  dsimp only at hShell
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let w := actualOriginMatchedKummerValue K (L / a) B Fo J.1 J.2
  let v := actualOriginMatchedKummerPullback K a (L / a) B Fo J.1 J.2
  let d := fun r => actualHartreeTwoChannelInner Fp Fm hp hm r - v r
  let E := actualMatchedKummerShellError mu theta a R d
  have hCert : ActualOriginMatchedKummerCertificate K (L / a) B Fo J.1 J.2 := hpCert
  have hKummerNonneg : 0 ≤ actualInnerShellKummerConstant mu theta := by
    have hV : 0 ≤ actualInnerShellValueConstant := by
      unfold actualInnerShellValueConstant
      positivity
    have hD : 0 ≤ actualInnerShellDerivativeConstant := by
      unfold actualInnerShellDerivativeConstant
      positivity
    unfold actualInnerShellKummerConstant
    positivity
  have hFactor := actual_Hartree_backward_shell_relative_factor L a
    actualInnerShellEquationConstant (actualInnerShellKummerConstant mu theta)
    (by linarith) ha3 hKummerNonneg
  have hNormNonneg : 0 ≤ innerWeightedNorm (7 / 4 : ℝ) Fp +
      innerWeightedNorm (7 / 4 : ℝ) Fm :=
    add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  unfold ActualMomentLockedPhysicalBackwardShellConclusion
  dsimp only
  refine ⟨hp, hm, hShell.1, ?_, ?_⟩
  · calc
      innerWeightedNorm (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ≤
          20 * Cshell *
            (actualInnerShellEquationConstant * R ^ (-(3 / 4 : ℝ)) +
              actualInnerShellKummerConstant mu theta * R ^ (13 / 4 : ℝ) / a ^ 2) *
            (innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm) := hShell.2.1
      _ ≤ 20 * Cshell *
            ((actualInnerShellEquationConstant + actualInnerShellKummerConstant mu theta) *
              R ^ (-(3 / 4 : ℝ))) *
            (innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hFactor (by positivity)) hNormNonneg
      _ = _ := by ring
  · have hClass := actual_origin_matched_Kummer_classical_on_positive_interval
      K hr0 hLB.le hBOne Fo hFo J.1 J.2 B ⟨hB, hBOne⟩
    change actualOriginOutgoingTrace K B (w B) (deriv w B) = 0
    rw [hClass.1.deriv]
    exact hCert.2.2.1

end HBL.TypeIIDynamicSelection
