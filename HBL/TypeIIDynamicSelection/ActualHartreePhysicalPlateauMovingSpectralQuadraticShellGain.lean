import HBL.TypeIIDynamicSelection.ActualHartreeMatchedBackwardQuadraticSpectralWeighted
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedKummerPullback
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedPlateauSource
import Mathlib.Tactic

/-!
# Actual quartic Hartree plateau: quadratic moving-spectral forcing on the backward shell

The unchanged physical quartic source, the real modulation speed terms,
the two Fredholm channels, and the common original Kummer continuation
are retained in a single object.  The exact plateau PDE identity PRODUCES
the same-source relation required by the backward quadratic Green estimate;
it is not assumed as a separate envelope or source cancellation.

The output is the weighted spatial bound for -a^(-2) delta*u1,
u1 = G_K[delta*u0;0,0].  This is the surviving source for the CURRENT
moving spectral coefficient, not for the original frozen coefficient.
The theorem makes no time decay or global four-region claim.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.Profile.Kummer HBL.L2Kernel

theorem actual_Hartree_true_plateau_moving_spectral_quadratic_backward_shell_norm
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B ell c a db dw C G : ℝ) (z : ℝ → ℂ)
    (hp0 : InWeightedL2 (7 / 4 : ℝ)
      (actualHartreeTransmissionPlusSource ell c z))
    (hm0 : InWeightedL2 (7 / 4 : ℝ)
      (actualHartreeTransmissionMinusSource ell c z))
    (hcp0 : Continuous (actualHartreeTransmissionPlusSource ell c z))
    (hcm0 : Continuous (actualHartreeTransmissionMinusSource ell c z))
    (hLarge : 4 < actualHartreeSlowInnerRadius ell)
    (ha : 0 < a)
    (hLB : actualHartreeSlowInnerRadius ell / a ≤ B)
    (hB : B < scale)
    (hG : 0 ≤ G)
    (hBasis : OriginBasisOn K
       (actualHartreeSlowInnerRadius ell / a) B C)
    (hModes : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (hSmall : 16 * (actualHartreeSlowInnerRadius ell / 2) ^ 2 *
      ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1)
    (hFo : ∀ r ∈ Ioo (0 : ℝ) scale,
      ContinuousAt
        (fun t => -actualHartreeLaplacianScaledKummerSource a ell c z t -
          (db : ℂ) * actualMomentLockedScaledScaleSource a c t -
          (dw : ℂ) * actualMomentLockedScaledPhaseSource a c t) r)
    (delta : ℂ)
    (hInt : ∀ (U DU : ℂ) (x : ℝ),
      x ∈ Icc ((actualHartreeSlowInnerRadius ell / a) / 2)
        (actualHartreeSlowInnerRadius ell / a) →
      IntervalIntegrable
        (originGreenSourceA K
          (fun t => delta * actualOriginMatchedKummerValue K
            (actualHartreeSlowInnerRadius ell / a) B
            (fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r -
              (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
              (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r)
            U DU t))
        volume x (actualHartreeSlowInnerRadius ell / a))
    (hIntR : ∀ (U DU : ℂ),
      IntervalIntegrable
        (originGreenSourceA K
          (fun t => delta * actualOriginMatchedKummerValue K
            (actualHartreeSlowInnerRadius ell / a) B
            (fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r -
              (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
              (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r)
            U DU t))
        volume (actualHartreeSlowInnerRadius ell / a) B)
    (hMeas : ∀ (U DU : ℂ),
      Measurable (fun y : ℝ =>
        (((a ^ 2)⁻¹ : ℝ) : ℂ) *
          (delta * actualOriginMatchedKummerValue K
            (actualHartreeSlowInnerRadius ell / a) B
            (fun x => delta * actualOriginMatchedKummerValue K
              (actualHartreeSlowInnerRadius ell / a) B
              (fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r -
                (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
                (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r)
              U DU x)
            0 0 (y / a)))) :
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
      let r0 := L / a
      let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r0
      let u0 := actualOriginMatchedKummerValue K r0 B Fo J.1 J.2
      let u1 := actualOriginMatchedKummerValue K r0 B
        (fun x => delta * u0 x) 0 0
      let E : ℝ → ℂ := fun y =>
        (((a ^ 2)⁻¹ : ℝ) : ℂ) * (delta * u1 (y / a))
      let D := actualInnerShellValueConstant *
        (innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm) +
        8 * R ^ 2 * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
      let A := ((a ^ 2)⁻¹ * ‖delta‖) *
        (2 * G ^ 2 * (r0 * ‖delta‖ * D))
      InWeightedL2 (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ∧
        innerWeightedNorm (7 / 4 : ℝ)
          (actualConjugatedShellMagnitude R E) ≤
          20 * R ^ (13 / 4 : ℝ) * A := by
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
  -- Keep the jet at the literal anchor required by the quadratic Green theorem.
  -- The physical equality 2 * R = L is applied only when converting the output.
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)
  let v := actualOriginMatchedKummerPullback K a (L / a) B Fo J.1 J.2
  let U : Set ℝ := Ioo 0 (a * scale)
  have hR : 2 < R := by dsimp [R, L]; linarith
  have hRpos : 0 < R := by linarith
  have hTwoR : 2 * R = L := by dsimp [R]; ring
  have hLupper : L < a * scale := by
    have h := (div_lt_iff₀ ha).1 (hLB.trans_lt hB)
    simpa only [mul_comm] using h
  have hSub : Icc R (2 * R) ⊆ U := by
    intro x hx
    have hxL : x ≤ L := hx.2.trans_eq hTwoR
    exact ⟨hRpos.trans_le hx.1, hxL.trans_lt hLupper⟩
  have hClass := actual_Hartree_matched_Kummer_pullback_classical K a ha
    (div_pos hL ha) hLB hB Fo hFo J.1 J.2
  have hSame : ∀ x ∈ Icc R (2 * R),
      actualMatchedScaledKummerApply mu theta a v x =
        -actualHartreeTwoChannelPhysicalSource Fp Fm x := by
    intro x hx
    rw [(hClass x (hSub hx)).2.2]
    have hPlateau : ((a ^ 2)⁻¹ : ℝ) • Fo (x / a) +
      actualHartreeTwoChannelPhysicalSource Fp Fm x = 0 :=
      actual_Hartree_moment_locked_plateau_scaled_source
        a ell c z x db dw ha hL (hSub hx).1
          (hx.2.trans_eq hTwoR)
    exact eq_neg_of_add_eq_zero_left hPlateau
  have hSmallR : 16 * R ^ 2 *
      ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1 := hSmall
  have hBasisR : OriginBasisOn K (2 * R / a) B C := by
    rw [hTwoR]
    exact hBasis
  have hInt' : ∀ x ∈ Icc ((2 * R / a) / 2) (2 * R / a),
      IntervalIntegrable
        (originGreenSourceA K
          (fun t => delta * actualOriginMatchedKummerValue K
            (2 * R / a) B Fo J.1 J.2 t))
        volume x (2 * R / a) := by
    rw [hTwoR]
    intro x hx
    exact hInt J.1 J.2 x hx
  have hIntR' : IntervalIntegrable
      (originGreenSourceA K
        (fun t => delta * actualOriginMatchedKummerValue K
          (2 * R / a) B Fo J.1 J.2 t))
      volume (2 * R / a) B := by
    rw [hTwoR]
    exact hIntR J.1 J.2
  have hMeas' : ∀ U DU : ℂ,
      Measurable (fun y : ℝ =>
        (((a ^ 2)⁻¹ : ℝ) : ℂ) *
          (delta * actualOriginMatchedKummerValue K (2 * R / a) B
            (fun x => delta * actualOriginMatchedKummerValue K
              (2 * R / a) B Fo U DU x) 0 0 (y / a))) := by
    rw [hTwoR]
    exact hMeas
  have hSame' : ∀ y ∈ Icc R (2 * R),
      actualMatchedScaledKummerApply mu theta a
        (actualOriginMatchedKummerPullback K a (2 * R / a) B Fo
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).1
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).2) y =
      -actualHartreeTwoChannelPhysicalSource Fp Fm y := by
    simpa only [hTwoR, J, v] using hSame
  have hResult := actual_Hartree_matched_backward_quadratic_spectral_source_weighted
    K a R B C G ha hR (by rw [hTwoR]; exact hLB) hB
    hG hBasisR hModes hSmallR
    Fp Fm hp hm hcp hcm Fo hFo hSame' delta hInt' hIntR' hMeas'
  simpa only [hTwoR, L, R, Fp, Fm, Fo] using hResult

/-- Under the same physical separation a >= (2R)^3, the actual
quadratic Volterra shell coefficient has a *negative* power of the
physical radius. This is strictly a spatial statement and contains
no presupposed modulation-time rate. -/
theorem actual_Hartree_quadratic_backward_shell_cubic_spatial_factor
    (a R G D : ℝ) (delta : ℂ)
    (hR : 2 < R) (hCubic : (2 * R) ^ 3 ≤ a)
    (hD : 0 ≤ D) :
    20 * R ^ (13 / 4 : ℝ) *
        ((a ^ 2)⁻¹ * ‖delta‖) *
        (2 * G ^ 2 * ((2 * R / a) * ‖delta‖ * D)) ≤
      (5 / 32 : ℝ) * G ^ 2 * R ^ (-(19 / 4 : ℝ)) *
        ‖delta‖ ^ 2 * D := by
  have hRpos : 0 < R := by linarith
  have hapos : 0 < a :=
    (pow_pos (by positivity : 0 < 2 * R) 3).trans_le hCubic
  have hbase : 0 ≤ (2 * R) ^ 3 := by positivity
  have hden : (2 * R) ^ 9 ≤ a ^ 3 := by
    have h := pow_le_pow_left₀ hbase hCubic 3
    convert h using 1 <;> ring
  have hR9 : 0 < (2 * R) ^ 9 := by positivity
  have hpow : R ^ (17 / 4 : ℝ) / R ^ 9 =
      R ^ (-(19 / 4 : ℝ)) := by
    rw [← Real.rpow_natCast R 9, ← Real.rpow_sub hRpos]
    norm_num
  have hfactor : R ^ (17 / 4 : ℝ) / a ^ 3 ≤
      R ^ (-(19 / 4 : ℝ)) / 512 := by
    calc
      R ^ (17 / 4 : ℝ) / a ^ 3 ≤
          R ^ (17 / 4 : ℝ) / (2 * R) ^ 9 :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hRpos.le _)
          hR9 hden
      _ = (R ^ (17 / 4 : ℝ) / R ^ 9) / 512 := by
        have h9 : (2 * R) ^ 9 = 512 * R ^ 9 := by ring
        rw [h9, mul_comm (512 : ℝ) (R ^ 9), div_mul_eq_div_div]
      _ = R ^ (-(19 / 4 : ℝ)) / 512 := by rw [hpow]
  have hpower : R ^ (13 / 4 : ℝ) * R =
      R ^ (17 / 4 : ℝ) := by
    rw [← Real.rpow_one R, ← Real.rpow_add hRpos]
    norm_num
  have hcoef : 0 ≤ 80 * G ^ 2 * ‖delta‖ ^ 2 * D := by positivity
  calc
    20 * R ^ (13 / 4 : ℝ) *
          ((a ^ 2)⁻¹ * ‖delta‖) *
          (2 * G ^ 2 * ((2 * R / a) * ‖delta‖ * D)) =
        (80 * G ^ 2 * ‖delta‖ ^ 2 * D) *
          ((R ^ (13 / 4 : ℝ) * R) / a ^ 3) := by
      field_simp [hapos.ne']
      ring
    _ = (80 * G ^ 2 * ‖delta‖ ^ 2 * D) *
          (R ^ (17 / 4 : ℝ) / a ^ 3) := by rw [hpower]
    _ ≤ (80 * G ^ 2 * ‖delta‖ ^ 2 * D) *
          (R ^ (-(19 / 4 : ℝ)) / 512) :=
      mul_le_mul_of_nonneg_left hfactor hcoef
    _ = (5 / 32 : ℝ) * G ^ 2 * R ^ (-(19 / 4 : ℝ)) *
          ‖delta‖ ^ 2 * D := by ring



/-- The SAME physical quartic source and actual zero-Cauchy spectral
Volterra field, with the original separation a >= L^3, give a
negative-radius weighted norm. No independent source budget, frozen-time
decay rate, or Type-II speed law is assumed. -/
theorem actual_Hartree_true_plateau_moving_spectral_quadratic_cubic_shell_gain
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B ell c a db dw C G : ℝ) (z : ℝ → ℂ)
    (hp0 : InWeightedL2 (7 / 4 : ℝ)
      (actualHartreeTransmissionPlusSource ell c z))
    (hm0 : InWeightedL2 (7 / 4 : ℝ)
      (actualHartreeTransmissionMinusSource ell c z))
    (hcp0 : Continuous (actualHartreeTransmissionPlusSource ell c z))
    (hcm0 : Continuous (actualHartreeTransmissionMinusSource ell c z))
    (hLarge : 4 < actualHartreeSlowInnerRadius ell)
    (ha : 0 < a)
    (hLB : actualHartreeSlowInnerRadius ell / a ≤ B)
    (hB : B < scale)
    (hG : 0 ≤ G)
    (hBasis : OriginBasisOn K
       (actualHartreeSlowInnerRadius ell / a) B C)
    (hModes : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (hSmall : 16 * (actualHartreeSlowInnerRadius ell / 2) ^ 2 *
      ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1)
    (hCubic : actualHartreeSlowInnerRadius ell ^ 3 ≤ a)
    (hFo : ∀ r ∈ Ioo (0 : ℝ) scale,
      ContinuousAt
        (fun t => -actualHartreeLaplacianScaledKummerSource a ell c z t -
          (db : ℂ) * actualMomentLockedScaledScaleSource a c t -
          (dw : ℂ) * actualMomentLockedScaledPhaseSource a c t) r)
    (delta : ℂ)
    (hInt : ∀ (U DU : ℂ) (x : ℝ),
      x ∈ Icc ((actualHartreeSlowInnerRadius ell / a) / 2)
        (actualHartreeSlowInnerRadius ell / a) →
      IntervalIntegrable
        (originGreenSourceA K
          (fun t => delta * actualOriginMatchedKummerValue K
            (actualHartreeSlowInnerRadius ell / a) B
            (fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r -
              (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
              (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r)
            U DU t))
        volume x (actualHartreeSlowInnerRadius ell / a))
    (hIntR : ∀ (U DU : ℂ),
      IntervalIntegrable
        (originGreenSourceA K
          (fun t => delta * actualOriginMatchedKummerValue K
            (actualHartreeSlowInnerRadius ell / a) B
            (fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r -
              (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
              (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r)
            U DU t))
        volume (actualHartreeSlowInnerRadius ell / a) B)
    (hMeas : ∀ (U DU : ℂ),
      Measurable (fun y : ℝ =>
        (((a ^ 2)⁻¹ : ℝ) : ℂ) *
          (delta * actualOriginMatchedKummerValue K
            (actualHartreeSlowInnerRadius ell / a) B
            (fun x => delta * actualOriginMatchedKummerValue K
              (actualHartreeSlowInnerRadius ell / a) B
              (fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r -
                (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
                (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r)
              U DU x)
            0 0 (y / a)))) :
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
      let r0 := L / a
      let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r0
      let u0 := actualOriginMatchedKummerValue K r0 B Fo J.1 J.2
      let u1 := actualOriginMatchedKummerValue K r0 B
        (fun x => delta * u0 x) 0 0
      let E : ℝ → ℂ := fun y =>
        (((a ^ 2)⁻¹ : ℝ) : ℂ) * (delta * u1 (y / a))
      let D := actualInnerShellValueConstant *
        (innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm) +
        8 * R ^ 2 * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
      InWeightedL2 (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ∧
        innerWeightedNorm (7 / 4 : ℝ)
          (actualConjugatedShellMagnitude R E) ≤
          (5 / 32 : ℝ) * G ^ 2 * R ^ (-(19 / 4 : ℝ)) *
            ‖delta‖ ^ 2 * D := by
  -- Exact same quartic source and two real Fredholm forcing channels.
  -- The nonnegativity of D is derived from the actual weighted norms.
  have hOriginal :=
    actual_Hartree_true_plateau_moving_spectral_quadratic_backward_shell_norm
      K B ell c a db dw C G z hp0 hm0 hcp0 hcm0 hLarge
      ha hLB hB hG hBasis hModes hSmall hFo delta hInt hIntR hMeas
  dsimp only at hOriginal ⊢
  obtain ⟨hp, hm, hMem, hBound⟩ := hOriginal
  refine ⟨hp, hm, hMem, ?_⟩
  let L := actualHartreeSlowInnerRadius ell
  let R := L / 2
  let Fp := fun r => actualHartreeTransmissionPlusSource ell c z r +
    dw * actualMomentLockedInnerPhaseSource L c r
  let Fm := fun r => actualHartreeTransmissionMinusSource ell c z r +
    db * actualMomentLockedInnerScaleSource L c r
  let D := actualInnerShellValueConstant *
      (innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm) +
    8 * R ^ 2 * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
  have hR : 2 < R := by dsimp [R, L]; linarith
  have hTwoR : 2 * R = L := by dsimp [R]; ring
  have hCubicR : (2 * R) ^ 3 ≤ a := by
    rw [hTwoR]
    exact hCubic
  have hValue : 0 ≤ actualInnerShellValueConstant := by
    unfold actualInnerShellValueConstant
    positivity
  have hDeriv : 0 ≤ actualInnerShellDerivativeConstant := by
    unfold actualInnerShellDerivativeConstant
    positivity
  have hEquation : 0 ≤ actualInnerShellEquationConstant := by
    unfold actualInnerShellEquationConstant
    positivity
  have hKummer : 0 ≤ actualInnerShellKummerConstant mu theta := by
    unfold actualInnerShellKummerConstant
    positivity
  have hN : 0 ≤ innerWeightedNorm (7 / 4 : ℝ) Fp +
      innerWeightedNorm (7 / 4 : ℝ) Fm :=
    add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hBudget : 0 ≤
      actualHartreeTwoChannelShellBudget mu theta a R Fp Fm := by
    unfold actualHartreeTwoChannelShellBudget
    have hRad : 0 < R := by linarith
    have hCoefficient :
        0 ≤ actualInnerShellEquationConstant / R ^ 4 +
          actualInnerShellKummerConstant mu theta / a ^ 2 :=
      add_nonneg (div_nonneg hEquation (pow_nonneg hRad.le 4))
        (div_nonneg hKummer (sq_nonneg a))
    exact mul_nonneg hCoefficient hN
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg (mul_nonneg hValue hN)
      (mul_nonneg (by positivity : 0 ≤ 8 * R ^ 2) hBudget)
  have hSpatial := actual_Hartree_quadratic_backward_shell_cubic_spatial_factor
    a R G D delta hR hCubicR hD
  rw [hTwoR] at hSpatial
  exact hBound.trans hSpatial

end HBL.TypeIIDynamicSelection
