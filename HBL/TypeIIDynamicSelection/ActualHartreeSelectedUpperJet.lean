import HBL.TypeIIDynamicSelection.ActualHartreeSelectedSpeedBound
import HBL.TypeIIDynamicSelection.ActualHartreeKummerUpperJetBound
import HBL.TypeIIDynamicSelection.ActualHartreeSpeedRegularGreen
import HBL.TypeIIDynamicSelection.ActualHartreeCanonicalJetBound
import Mathlib.Tactic

/-!
# Selected compatible source gives a controlled upper Kummer jet

This theorem is a reusable source-to-jet bridge. The full compatibility
matrix selects the unique real speed correction. The adjusted inner source,
its canonical Fredholm jet, and the two genuine speed-direction regular
Green coefficients are controlled by the original source data.

The only extra input is a quantitative regular-Green bound for the baseline
outer source. For the actual Hartree source this is supplied by
actual_Hartree_scaled_Kummer_regular_Green_tail_gain.

No selected-speed size, adjusted-source size, obstruction size, or upper
Kummer jet is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

def actualHartreeSelectedUpperJetBasisConstant (D G B : ℝ) : ℝ :=
  (1 + (D + 1) * G * B ^ 2) + 2 * ((D + 1) * G) * B ^ 2

theorem actual_Hartree_selected_upper_regular_jet_region
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B)
    (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < C ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
      ∀ (Fp Fm : ℝ → ℝ)
        (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
        Continuous Fp → Continuous Fm →
      ∀ (F : ℝ → ℂ) (Q Kreg : ℝ), 0 ≤ Q → 0 ≤ Kreg →
        IntervalIntegrable F volume (L / a) B →
        (∀ r ∈ Icc (L / a) B, ‖F r‖ ≤ Q / r ^ 2) →
        ‖originGreenCoeffB K (L / a) F B‖ ≤
          Kreg * (innerWeightedNorm (7 / 4 : ℝ) Fp +
            innerWeightedNorm (7 / 4 : ℝ) Fm + Q) →
        ∃ p : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F p.1 p.2 = 0 ∧
          (∀ q : ℝ × ℝ,
            actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
              Fp Fm hp hm F q.1 q.2 = 0 → q = p) ∧
          let Gp := actualMomentLockedInnerPhaseSource L c
          let Gm := actualMomentLockedInnerScaleSource L c
          let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp
          let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp
          let Fpa := fun r => Fp r + p.2 * Gp r
          let Fma := fun r => Fm r + p.1 * Gm r
          let hpa := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp p.2
          let hma := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm p.1
          let S := actualMomentLockedScaledScaleSource a c
          let P := actualMomentLockedScaledPhaseSource a c
          let Fo := fun r => F r + (-(p.1 : ℂ)) * S r + (-(p.2 : ℂ)) * P r
          let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
          ‖actualOriginMatchedKummerValue K (L / a) B Fo J.1 J.2 B‖ +
            B * ‖actualOriginMatchedKummerSlope K (L / a) B Fo J.1 J.2 B‖ ≤
          actualHartreeSelectedUpperJetBasisConstant D G B *
            (C + Kreg) *
            (innerWeightedNorm (7 / 4 : ℝ) Fp +
              innerWeightedNorm (7 / 4 : ℝ) Fm + Q) := by
  obtain ⟨Lc, ec, Cc, hLc, hec, hecOne, hCc, hCorrect⟩ :=
    actual_Hartree_selected_corrected_source_bounds_region
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨Ls, es, Cs, hLs, hes, hesOne, hCs, hSpeedSelect⟩ :=
    actual_Hartree_selected_speed_original_bound_region
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨Cg, hCg, hSpeedGreen⟩ :=
    actual_Hartree_speed_regular_Green_coefficients
  let Jc : ℝ := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
  let Sconst : ℝ := Cs * Cg * G * B
  let C : ℝ := 1 + 2 * G * Jc * Cc + Sconst
  have hJc : 0 ≤ Jc := by
    dsimp [Jc, actualInnerShellValueConstant, actualInnerShellDerivativeConstant]
    positivity
  have hSconst : 0 ≤ Sconst := by
    dsimp [Sconst]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let L0 := max Lc Ls
  let epsilon := min ec es
  have hL0 : 6 ≤ L0 := hLc.trans (le_max_left _ _)
  have heps : 0 < epsilon := lt_min hec hes
  have hepsOne : epsilon ≤ 1 :=
    (min_le_left _ _).trans hecOne
  refine ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, ?_⟩
  intro L c a hLp hLarge ha3 hSmall
    Fp Fm hp hm hcp hcm F Q Kreg hQ hKreg hF hEnvelope hBase
  have hLargeC : Lc ≤ L := (le_max_left _ _).trans hLarge
  have hLargeS : Ls ≤ L := (le_max_right _ _).trans hLarge
  have hSmallC : a * |c| ≤ ec := hSmall.trans (min_le_left _ _)
  have hSmallS : a * |c| ≤ es := hSmall.trans (min_le_right _ _)
  have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
  have hLsix : 6 ≤ L := hL0.trans hLarge
  have hLtwo : 2 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  let N0 := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let E := N0 + Q
  have hN0 : 0 ≤ N0 := add_nonneg
    (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hE : 0 ≤ E := add_nonneg hN0 hQ
  obtain ⟨p, Qa, hCompat, hUnique, hQa, hLB, _hEnv, hSize⟩ :=
    hCorrect L c a hLp hLargeC ha3 hSmallC
      Fp Fm hp hm hcp hcm F Q hQ hF hEnvelope
  obtain ⟨q, hCompatQ, _hUniqueQ, hSpeedQ⟩ :=
    hSpeedSelect L c a hLp hLargeS ha3 hSmallS
      Fp Fm hp hm hcp hcm F Q hQ hF hEnvelope
  have hqp : q = p := hUnique q hCompatQ
  subst q
  have hSpeed : |p.1| + |p.2| ≤ (Cs / a) * E := by
    simpa only [N0, E] using hSpeedQ
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp
  let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp
  let Fpa := fun r => Fp r + p.2 * Gp r
  let Fma := fun r => Fm r + p.1 * Gm r
  let hpa := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp p.2
  let hma := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm p.1
  let Nadj := innerWeightedNorm (7 / 4 : ℝ) Fpa +
    innerWeightedNorm (7 / 4 : ℝ) Fma
  have hNadj : Nadj ≤ Cc * E := by
    dsimp [Nadj, Fpa, Fma, Gp, Gm, E, N0] at hSize ⊢
    nlinarith only [hSize, hQa]
  have hSpeedCont := actual_Hartree_moment_locked_inner_sources_continuous L c
  have hcpa : Continuous Fpa := by
    dsimp [Fpa, Gp]
    exact hcp.add (continuous_const.mul hSpeedCont.2)
  have hcma : Continuous Fma := by
    dsimp [Fma, Gm]
    exact hcm.add (continuous_const.mul hSpeedCont.1)
  let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
  have hJraw :=
    actual_Hartree_canonical_inner_jet_source_norm_bound
      Fpa Fma hpa hma hcpa hcma L a hLtwo ha
  have hJ :
      ‖J.1‖ + (L / a) * ‖J.2‖ ≤ Jc * (Cc * E) := by
    have hmul := mul_le_mul_of_nonneg_left hNadj hJc
    simpa only [J, Jc, Nadj] using hJraw.trans hmul
  let S := actualMomentLockedScaledScaleSource a c
  let P := actualMomentLockedScaledPhaseSource a c
  let Fo := fun r => F r + (-(p.1 : ℂ)) * S r + (-(p.2 : ℂ)) * P r
  have hr0 : 0 < L / a := div_pos hLp ha
  have hKBasis :=
    origin_kummer_annulus_bound K (L / a) B G hr0 hBR hG hbound
  have hSpeedInt :=
    actual_Hartree_moment_locked_scaled_speed_integrable_on
      a c (L / a) B ha hr0 hLB
  have hF1 : IntervalIntegrable
      (fun r => F r + (-(p.1 : ℂ)) * S r) volume (L / a) B :=
    hF.add (hSpeedInt.1.const_mul (-(p.1 : ℂ)))
  have hCoeff1 :=
    actual_moment_locked_regular_source_coefficient_add_mul_on
      K hKBasis hLB F S hF hSpeedInt.1 (-(p.1 : ℂ))
  have hCoeff2 :=
    actual_moment_locked_regular_source_coefficient_add_mul_on
      K hKBasis hLB
      (fun r => F r + (-(p.1 : ℂ)) * S r) P
      hF1 hSpeedInt.2 (-(p.2 : ℂ))
  have hCoeffEq :
      originGreenCoeffB K (L / a) Fo B =
        originGreenCoeffB K (L / a) F B +
          (-(p.1 : ℂ)) * originGreenCoeffB K (L / a) S B +
          (-(p.2 : ℂ)) * originGreenCoeffB K (L / a) P B := by
    dsimp [Fo]
    rw [hCoeff2, hCoeff1]
  have hSG :=
    hSpeedGreen K G L c a B hG hLone ha hBOne hBR
      hSmallOne hLB hbound
  let SG : ℝ := Cg * G * a * B
  have hSG0 : 0 ≤ SG := by dsimp [SG]; positivity
  have hSpeedContribution :
      |p.1| * ‖originGreenCoeffB K (L / a) S B‖ +
        |p.2| * ‖originGreenCoeffB K (L / a) P B‖ ≤
      Sconst * E := by
    have h1 := mul_le_mul_of_nonneg_left hSG.1 (abs_nonneg p.1)
    have h2 := mul_le_mul_of_nonneg_left hSG.2 (abs_nonneg p.2)
    have hsum :
        |p.1| * ‖originGreenCoeffB K (L / a) S B‖ +
          |p.2| * ‖originGreenCoeffB K (L / a) P B‖ ≤
        (|p.1| + |p.2|) * SG := by
      dsimp [SG] at h1 h2 ⊢
      nlinarith only [h1, h2]
    have hscale :
        (|p.1| + |p.2|) * SG ≤ ((Cs / a) * E) * SG :=
      mul_le_mul_of_nonneg_right hSpeed hSG0
    calc
      _ ≤ (|p.1| + |p.2|) * SG := hsum
      _ ≤ ((Cs / a) * E) * SG := hscale
      _ = Sconst * E := by
        dsimp [SG, Sconst]
        field_simp [ha.ne']
  have hT :
      ‖originGreenCoeffB K (L / a) Fo B‖ ≤
        (Kreg + Sconst) * E := by
    rw [hCoeffEq]
    calc
      _ ≤ ‖originGreenCoeffB K (L / a) F B‖ +
          ‖(-(p.1 : ℂ)) * originGreenCoeffB K (L / a) S B‖ +
          ‖(-(p.2 : ℂ)) * originGreenCoeffB K (L / a) P B‖ :=
        (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) (le_refl _))
      _ = ‖originGreenCoeffB K (L / a) F B‖ +
          |p.1| * ‖originGreenCoeffB K (L / a) S B‖ +
          |p.2| * ‖originGreenCoeffB K (L / a) P B‖ := by
        simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      _ = ‖originGreenCoeffB K (L / a) F B‖ +
          (|p.1| * ‖originGreenCoeffB K (L / a) S B‖ +
            |p.2| * ‖originGreenCoeffB K (L / a) P B‖) := by ring
      _ ≤ Kreg * E + Sconst * E := add_le_add hBase hSpeedContribution
      _ = (Kreg + Sconst) * E := by ring
  have hZero :
      actualMomentLockedIntervalObstruction K (L / a) B Fo J.1 J.2 = 0 := by
    have hc0 := hCompat
    unfold actualMomentLockedCoupledCompatibility at hc0
    dsimp only at hc0
    change actualMomentLockedIntervalObstruction K (L / a) B
      (fun r => F r - (p.1 : ℂ) * S r - (p.2 : ℂ) * P r) J.1 J.2 = 0 at hc0
    have hFo :
        Fo = (fun r => F r - (p.1 : ℂ) * S r - (p.2 : ℂ) * P r) := by
      funext r
      dsimp [Fo]
      ring
    rw [hFo]
    exact hc0
  have hJ0 : 0 ≤ Jc * (Cc * E) := by positivity
  have hT0 : 0 ≤ (Kreg + Sconst) * E := by positivity
  have hUpper :=
    actual_matched_Kummer_upper_regular_jet_bound
      K D G B (L / a)
      (Jc * (Cc * E)) ((Kreg + Sconst) * E)
      hD hG hr0 hLB hBOne hBR hcoeff hbound
      Fo J.1 J.2 hZero hJ hJ0 hT hT0
  let Kbasis := actualHartreeSelectedUpperJetBasisConstant D G B
  have hKbasis : 0 ≤ Kbasis := by
    dsimp [Kbasis, actualHartreeSelectedUpperJetBasisConstant]
    positivity
  have hInside :
      2 * G * (Jc * (Cc * E)) + (Kreg + Sconst) * E ≤
        (C + Kreg) * E := by
    dsimp [C]
    nlinarith only [hE, hSconst,
      mul_nonneg hG (mul_nonneg hJc (mul_nonneg hCc.le hE))]
  refine ⟨p, hCompat, hUnique, ?_⟩
  dsimp only
  have hFinal := hUpper.trans
    (mul_le_mul_of_nonneg_left hInside hKbasis)
  simpa only [Kbasis, actualHartreeSelectedUpperJetBasisConstant,
    J, Fo, S, P, Fpa, Fma, Gp, Gm, hpa, hma,
    Jc, Sconst, E, N0, mul_assoc] using hFinal

end HBL.TypeIIDynamicSelection
