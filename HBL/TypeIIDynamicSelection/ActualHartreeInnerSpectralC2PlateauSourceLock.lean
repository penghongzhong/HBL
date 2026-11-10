import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedPlateauSource
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralOriginalPDEMismatch
import HBL.TypeIIDynamicSelection.ActualHartreeSpectralCorrectedFourPieceThreeC1
import Mathlib.Tactic

/-!
# Actual same-PDE plateau source cancels in the INNER spectral C² mismatch

The original source is the *literal* inverse-square quartic Hartree
interaction with its actual two real modulation-speed directions.
Both inner Fredholm channels and the origin-normalized Kummer
source use this same full original physical interaction.

The existing strict plateau identification cancels the two
unshifted source terms pointwise even at the inner Cauchy join.
After spectral correction, the ONLY extra source in this
identification is the *actual* delta times the original
Cramer Green field. No curvature, derivative bound, time order,
physical orbit or Type-II rate is postulated here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- At every actual inner plateau point, the literal original Hartree
two-channel source cancels the true physical outer source. The source
left after the first spectral correction is exactly the correction
coefficient times the SAME original source-normalized Cramer Green
solution; no independent source is introduced. -/
theorem actual_Hartree_original_plateau_spectral_inner_C2_source_cancellation
    (a ell c : ℝ) (z : ℝ → ℂ) (y db dw : ℝ)
    (ha : 0 < a)
    (hL : 0 < actualHartreeSlowInnerRadius ell)
    (hy : 0 < y) (hyL : y ≤ actualHartreeSlowInnerRadius ell)
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B : ℝ) (U DU delta : ℂ) :
    let L := actualHartreeSlowInnerRadius ell
    let Fp := actualHartreeTransmissionPlusSource ell c z
    let Fm := actualHartreeTransmissionMinusSource ell c z
    let Gp := actualMomentLockedInnerPhaseSource L c
    let Gm := actualMomentLockedInnerScaleSource L c
    let Fo : ℝ → ℂ := fun r =>
      -actualHartreeLaplacianScaledKummerSource a ell c z r -
      (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
      (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
    let u0 := actualOriginMatchedKummerValue K (y / a) B Fo U DU
    ((a ^ 2)⁻¹ : ℝ) • (Fo (y / a) - delta * u0 (y / a)) +
      actualHartreeTwoChannelPhysicalSource
        (fun r => Fp r + dw * Gp r)
        (fun r => Fm r + db * Gm r) y =
      -((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) := by
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  let Fp := actualHartreeTransmissionPlusSource ell c z
  let Fm := actualHartreeTransmissionMinusSource ell c z
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  let Fo : ℝ → ℂ := fun r =>
    -actualHartreeLaplacianScaledKummerSource a ell c z r -
    (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
    (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
  let u0 := actualOriginMatchedKummerValue K (y / a) B Fo U DU
  have hSame :
      ((a ^ 2)⁻¹ : ℝ) • Fo (y / a) +
        actualHartreeTwoChannelPhysicalSource
          (fun r => Fp r + dw * Gp r)
          (fun r => Fm r + db * Gm r) y = 0 := by
    exact actual_Hartree_moment_locked_plateau_scaled_source
      a ell c z y db dw ha hL hy hyL
  change ((a ^ 2)⁻¹ : ℝ) •
      (Fo (y / a) - delta * u0 (y / a)) +
        actualHartreeTwoChannelPhysicalSource
          (fun r => Fp r + dw * Gp r)
          (fun r => Fm r + db * Gm r) y =
      -((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a))
  rw [smul_sub]
  calc
    ((a ^ 2)⁻¹ : ℝ) • Fo (y / a) -
        ((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) +
        actualHartreeTwoChannelPhysicalSource
          (fun r => Fp r + dw * Gp r)
          (fun r => Fm r + db * Gm r) y =
      (((a ^ 2)⁻¹ : ℝ) • Fo (y / a) +
        actualHartreeTwoChannelPhysicalSource
          (fun r => Fp r + dw * Gp r)
          (fun r => Fm r + db * Gm r) y) -
        ((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) := by abel
    _ = -((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) := by rw [hSame]; simp


/-- At a genuine C¹ inner interface the ORIGINAL physical Kummer
operator's source jump is exactly the radial curvature jump.
All drift, potential and parameter-dependent coefficients cancel.
This does not claim that the original Fredholm Hessian is this Kummer
operator; identifying that physical source remains a separate gate. -/
theorem actual_Hartree_inner_C1_curvature_jump_eq_original_source_jump
    (mu theta a L : ℝ) (u v : ℝ → ℂ)
    (hValue : u L = v L)
    (hSlope : deriv u L = deriv v L) :
    deriv (deriv u) L - deriv (deriv v) L =
      actualMatchedScaledKummerApply mu theta a u L -
        actualMatchedScaledKummerApply mu theta a v L := by
  unfold actualMatchedScaledKummerApply complexRadialLaplacian
  simp only [Complex.real_smul, hValue, hSlope]
  ring

/-- If the INNER original source and the spectrally corrected OUTER
original source have the exact first-order delta*u0 discrepancy,
their C¹ splice has precisely that second-jet defect. In particular
the first-order ORIGINAL PDE residual cannot be silently replaced by
a quadratic shifted-operator residual. No independent source bound
or a physical-orbit realization is assumed. -/
theorem actual_Hartree_inner_C1_spectral_curvature_jump_from_sources
    (mu theta a L : ℝ) (u v : ℝ → ℂ)
    (S delta u0 : ℂ)
    (hValue : u L = v L)
    (hSlope : deriv u L = deriv v L)
    (hInnerSource : actualMatchedScaledKummerApply mu theta a u L = S)
    (hCorrectedSource :
      actualMatchedScaledKummerApply mu theta a v L =
        S - ((a ^ 2)⁻¹ : ℝ) • (delta * u0)) :
    deriv (deriv u) L - deriv (deriv v) L =
      ((a ^ 2)⁻¹ : ℝ) • (delta * u0) := by
  rw [actual_Hartree_inner_C1_curvature_jump_eq_original_source_jump
    mu theta a L u v hValue hSlope, hInnerSource, hCorrectedSource]
  simp only [Complex.real_smul]
  ring


/-- The actual Fredholm two-channel INNER field and the actual Cramer
selected, spectrally corrected Kummer OUTER field meet with identical
value and slope, but their curvature jump is the exact ORIGINAL
physical Kummer operator on the same inner field minus the full
spectral source F - delta*u0. No independent source or curvature is
introduced; controlling the first term via the true Hartree Hessian
remains a distinct unproved PDE obligation. -/
theorem actual_Hartree_true_inner_spectral_C1_curvature_jump
    {mu theta scale B : ℝ} (K : OriginKummerPair mu theta scale)
    (L a : ℝ) (hL : 0 < L) (ha : 0 < a)
    (hOrder : L / a ≤ B) (hB : B < scale)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r)
    (d : ℂ) :
    let u := actualHartreeTwoChannelInner Fp Fm hp hm
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    let v := actualHartreeMatchedSpectralPhysicalValue K a (L / a) B
      F J.1 J.2 d
    deriv (deriv u) L - deriv (deriv v) L =
      actualMatchedScaledKummerApply mu theta a u L -
        ((a ^ 2)⁻¹ : ℝ) •
          (F (L / a) -
            d * actualOriginMatchedKummerValue K (L / a) B
              F J.1 J.2 (L / a)) := by
  dsimp only
  let u := actualHartreeTwoChannelInner Fp Fm hp hm
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let v0 := actualOriginMatchedKummerPullback K a (L / a) B F J.1 J.2
  let w := actualHartreeMatchedSpectralCorrectedValue
    K (L / a) B F J.1 J.2 d
  let v := actualHartreeMatchedSpectralPhysicalValue
    K a (L / a) B F J.1 J.2 d
  have hr0 : 0 < L / a := div_pos hL ha
  have hOld :=
    actual_Hartree_moment_locked_pullback_actual_inner_jet
      K L a hL ha hOrder hB Fp Fm hp hm F hF
  dsimp only at hOld
  have hOriginal :=
    actual_origin_matched_Kummer_actual_endpoint_jets
      K hr0 hOrder hB F hF J.1 J.2
  have hSelected :=
    actual_Hartree_matched_spectral_corrected_left_C1_and_exact_equation
      K (L / a) B hr0 hOrder hB F hF J.1 J.2 d
  dsimp only at hSelected
  have hJvalue : J.1 = u L := by
    calc
      J.1 = actualOriginMatchedKummerValue K (L / a) B F J.1 J.2 (L / a) :=
        hOriginal.1.symm
      _ = v0 L := rfl
      _ = u L := hOld.1
  have hValue : u L = v L := by
    calc
      u L = J.1 := hJvalue.symm
      _ = v L := hSelected.1.symm
  have hV0 : HasDerivAt v0 ((1 / a : ℝ) • J.2) L := by
    have h := hOriginal.2.1.scomp L ((hasDerivAt_id L).div_const a)
    have hV0' : HasDerivAt
        (fun y : ℝ =>
          actualOriginMatchedKummerValue K (L / a) B F J.1 J.2 (y / a))
        ((1 / a : ℝ) • J.2) L := by
      simpa only [Function.comp_def, id_eq, one_div,
        Complex.real_smul, Complex.ofReal_inv, mul_comm] using h
    change HasDerivAt
      (fun y : ℝ =>
        actualOriginMatchedKummerValue K (L / a) B F J.1 J.2 (y / a))
      ((1 / a : ℝ) • J.2) L
    exact hV0'
  have hV : HasDerivAt v ((1 / a : ℝ) • J.2) L := by
    have h := hSelected.2.1.scomp L ((hasDerivAt_id L).div_const a)
    have hV' : HasDerivAt
        (fun y : ℝ =>
          actualHartreeMatchedSpectralCorrectedValue
            K (L / a) B F J.1 J.2 d (y / a))
        ((1 / a : ℝ) • J.2) L := by
      simpa only [Function.comp_def, id_eq, one_div,
        Complex.real_smul, Complex.ofReal_inv] using h
    change HasDerivAt
      (fun y : ℝ =>
        actualHartreeMatchedSpectralCorrectedValue
          K (L / a) B F J.1 J.2 d (y / a))
      ((1 / a : ℝ) • J.2) L
    exact hV'
  have hSlope : deriv u L = deriv v L := by
    rw [hV.deriv, hV0.unique hOld.2.1]
  have hRange : L < a * scale := by
    have h := (div_lt_iff₀ ha).1 (hOrder.trans_lt hB)
    simpa only [mul_comm] using h
  have hPDE :=
    actual_Hartree_matched_spectral_original_physical_source
      K a (L / a) B ha hr0 hOrder hB F hF J.1 J.2 d L
      ⟨hL, hRange⟩
  have hJump :=
    actual_Hartree_inner_C1_curvature_jump_eq_original_source_jump
      mu theta a L u v hValue hSlope
  change actualMatchedScaledKummerApply mu theta a v L =
    ((a ^ 2)⁻¹ : ℝ) •
      (F (L / a) -
        d * actualOriginMatchedKummerValue K (L / a) B
          F J.1 J.2 (L / a)) at hPDE
  rw [hPDE] at hJump
  exact hJump


/-- This gives an ACTUAL source-faithful curvature budget by composing the
old genuine original two-channel Kummer defect theorem, the exact
Cramer/spectral inner C¹ jump, and the same-source plateau identity.
The latter is an equality (not an assumed decay envelope); it is
produced by the existing physical Hartree plateau theorem when the
two source channels and selected real speeds agree. This theorem
does not claim decay for their weighted norms or the spectral shift. -/
theorem actual_Hartree_true_inner_spectral_C2_jump_native_shell_budget
    {mu theta scale B : ℝ} (K : OriginKummerPair mu theta scale)
    (L a R : ℝ) (hL : 0 < L) (ha : 0 < a)
    (hOrder : L / a ≤ B) (hB : B < scale)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (hFp : Continuous Fp) (hFm : Continuous Fm)
    (hR : 2 < R) (hRL : R ≤ L)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r)
    (d : ℂ)
    (hSameSource :
      ((a ^ 2)⁻¹ : ℝ) • F (L / a) +
        actualHartreeTwoChannelPhysicalSource Fp Fm L = 0) :
    let u := actualHartreeTwoChannelInner Fp Fm hp hm
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    let v := actualHartreeMatchedSpectralPhysicalValue K a (L / a) B
      F J.1 J.2 d
    ‖deriv (deriv u) L - deriv (deriv v) L‖ ≤
      actualHartreeTwoChannelShellBudget mu theta a R Fp Fm +
        ((a ^ 2)⁻¹ : ℝ) * ‖d‖ *
          ‖actualOriginMatchedKummerValue K (L / a) B
              F J.1 J.2 (L / a)‖ := by
  dsimp only
  let u := actualHartreeTwoChannelInner Fp Fm hp hm
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let v := actualHartreeMatchedSpectralPhysicalValue
    K a (L / a) B F J.1 J.2 d
  let U : ℂ :=
    actualOriginMatchedKummerValue K (L / a) B F J.1 J.2 (L / a)
  let S : ℂ := actualHartreeTwoChannelPhysicalSource Fp Fm L
  have hDelta :=
    actual_Hartree_true_inner_spectral_C1_curvature_jump
      K L a hL ha hOrder hB Fp Fm hp hm F hF d
  dsimp only at hDelta
  have hNative :=
    actual_Hartree_two_channel_inner_Kummer_defect_bound
      mu theta a Fp Fm hp hm hFp hFm R L hR hRL
  have hSame : ((a ^ 2)⁻¹ : ℝ) • F (L / a) + S = 0 :=
    hSameSource
  have hEq :
      deriv (deriv u) L - deriv (deriv v) L =
        (actualMatchedScaledKummerApply mu theta a u L + S) +
          ((a ^ 2)⁻¹ : ℝ) • (d * U) := by
    rw [hDelta]
    simp only [Complex.real_smul] at hSame ⊢
    linear_combination -hSame
  have hCoeff : 0 ≤ (a ^ 2)⁻¹ := by positivity
  have hScaledNorm :
      ‖((a ^ 2)⁻¹ : ℝ) • (d * U)‖ =
        ((a ^ 2)⁻¹ : ℝ) * ‖d‖ * ‖U‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hCoeff, norm_mul]
    ring
  calc
    ‖deriv (deriv u) L - deriv (deriv v) L‖ =
        ‖(actualMatchedScaledKummerApply mu theta a u L + S) +
          ((a ^ 2)⁻¹ : ℝ) • (d * U)‖ := congrArg norm hEq
    _ ≤ ‖actualMatchedScaledKummerApply mu theta a u L + S‖ +
        ‖((a ^ 2)⁻¹ : ℝ) • (d * U)‖ := norm_add_le _ _
    _ ≤ actualHartreeTwoChannelShellBudget mu theta a R Fp Fm +
        ((a ^ 2)⁻¹ : ℝ) * ‖d‖ * ‖U‖ := by
      rw [hScaledNorm]
      exact add_le_add hNative le_rfl

end HBL.TypeIIDynamicSelection
