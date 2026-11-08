import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedFullSingularGreenGain
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedCorrectedNorm
import Mathlib.Tactic

/-!
# Original source-only bound for the complete compatible singular Green channel

The genuine original inverse-square quartic Hartree source generates both
the uniquely selected speed and its corrected Fredholm and outer sources.
This combines (i) full, right-endpoint, original-Wronskian singular Green
transport and (ii) the actual selected corrected Fredholm weighted source
bound. Both use the SAME original source and the SAME unique real speed.
The adjusted inner norm is eliminated in favor of the original two-channel
norm and the original physical ell^(1/8) Hartree norm.

No positive power of a, no inverse moving matching radius, no assumed
blowup-rate and no arbitrary adjusted source-norm hypothesis remain.
This is the complete *singular component* of the fixed-time Kummer field;
the regular component, interface repair and full time-dependent Hartree PDE
remainder of order s^(-9/4) are separate.
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

theorem actual_Hartree_true_source_selected_full_singular_original_norm_gain
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧
        ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C Cs Cn : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
      0 < C ∧ 0 < Cs ∧ 0 < Cn ∧
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
        ∀ r ∈ Icc (L / a) B,
          let Fo : ℝ → ℂ := fun x =>
            F0 x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
              (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
          ‖originPhysicalValue K.y r *
              originGreenCoeffA K B Fo r‖ ≤
            (G * Cr * Cf * Cn + G * Cp + G ^ 2 * Cs * C) * (N + Q) := by
  obtain ⟨Lg, eg, C, Cs, hLg, heg, hegOne, hC, hCs, hFull⟩ :=
    actual_Hartree_true_source_selected_full_singular_Green_physical_no_scale_loss
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨Ln, en, Cn, hLn, hen, henOne, hCn, hNorm⟩ :=
    actual_Hartree_true_source_selected_corrected_inner_and_outer_norm
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  let L0 := max Lg Ln
  let epsilon := min eg en
  have hL0 : 6 ≤ L0 := hLg.trans (le_max_left _ _)
  have heps : 0 < epsilon := lt_min heg hen
  have hepsOne : epsilon ≤ 1 := (min_le_left _ _).trans hegOne
  refine ⟨L0, epsilon, C, Cs, Cn,
    hL0, heps, hepsOne, hC, hCs, hCn, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss
  dsimp only
  have hLargeG : Lg ≤ L := (le_max_left _ _).trans hLarge
  have hLargeN : Ln ≤ L := (le_max_right _ _).trans hLarge
  have hSmallG : a * |c| ≤ eg := hSmall.trans (min_le_left _ _)
  have hSmallN : a * |c| ≤ en := hSmall.trans (min_le_right _ _)
  obtain ⟨p, hCompat, hUnique, _hSize, hGreen⟩ :=
    hFull L c a hLp hLargeG ha3 hSmallG hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  obtain ⟨q, Qa, hCompatN, _hUniqueN, hQa, _hEnvelope, hCorrected⟩ :=
    hNorm L c a hLp hLargeN ha3 hSmallN hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  have hqp : q = p := hUnique q hCompatN
  subst q
  refine ⟨p, hCompat, hUnique, ?_⟩
  let F0 : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let Q : ℝ :=
    actualHartreePhysicalWeightedSourceConstant Bz Az * ell ^ (1 / 8 : ℝ)
  let N : ℝ :=
    innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let Cr : ℝ := 1 + (D + 1) * G * (B ^ 2 + 2)
  let Cp : ℝ := 1 + (D + 1) * G * B ^ 2
  let Cf : ℝ := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
  let Fpa := fun x => Fp x + p.2 * actualMomentLockedInnerPhaseSource L c x
  let Fma := fun x => Fm x + p.1 * actualMomentLockedInnerScaleSource L c x
  let Nadj := innerWeightedNorm (7 / 4 : ℝ) Fpa +
    innerWeightedNorm (7 / 4 : ℝ) Fma
  have hNormBound : Nadj + Qa ≤ Cn * (N + Q) := by
    simpa only [Nadj, Fpa, Fma, N, Q] using hCorrected
  have hNadj : Nadj ≤ Cn * (N + Q) := by linarith [hQa]
  have hN : 0 ≤ N :=
    add_nonneg (innerWeightedNorm_nonneg _ _)
      (innerWeightedNorm_nonneg _ _)
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hCf : 0 ≤ Cf := by
    dsimp [Cf, actualInnerShellValueConstant, actualInnerShellDerivativeConstant]
    positivity
  have hCoef : 0 ≤ G * Cr * Cf := by positivity
  have hQpart : G * Cp * Q ≤ G * Cp * (N + Q) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hN)
      (mul_nonneg hG hCp)
  have hTracePart :
      G * Cr * (Cf * Nadj) ≤
        G * Cr * (Cf * (Cn * (N + Q))) := by
    calc
      _ = (G * Cr * Cf) * Nadj := by ring
      _ ≤ (G * Cr * Cf) * (Cn * (N + Q)) :=
        mul_le_mul_of_nonneg_left hNadj hCoef
      _ = _ := by ring
  intro r hr
  let Fo : ℝ → ℂ := fun x =>
    F0 x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
      (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
  have hPhysical :
      ‖originPhysicalValue K.y r * originGreenCoeffA K B Fo r‖ ≤
        G * Cr * (Cf * Nadj) +
          (G * Cp * Q + (G ^ 2 * Cs * C) * (N + Q)) := by
    simpa only [Fo, Cr, Cp, Cf, Nadj, Fpa, Fma] using hGreen r hr
  calc
    ‖originPhysicalValue K.y r * originGreenCoeffA K B Fo r‖ ≤
        G * Cr * (Cf * Nadj) +
          (G * Cp * Q + (G ^ 2 * Cs * C) * (N + Q)) := hPhysical
    _ ≤ G * Cr * (Cf * (Cn * (N + Q))) +
          (G * Cp * (N + Q) +
            (G ^ 2 * Cs * C) * (N + Q)) :=
      add_le_add hTracePart (add_le_add hQpart le_rfl)
    _ = (G * Cr * Cf * Cn + G * Cp + G ^ 2 * Cs * C) * (N + Q) :=
      by ring

end HBL.TypeIIDynamicSelection
