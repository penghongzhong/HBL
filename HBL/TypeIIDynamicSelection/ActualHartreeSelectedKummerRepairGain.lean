import HBL.TypeIIDynamicSelection.ActualHartreeSelectedUpperJetTimeOrder
import HBL.TypeIIDynamicSelection.ActualKummerPhysicalRepairTimeGain
import Mathlib.Tactic

/-!
# Selected Kummer upper jet produces a next-layer physical interface repair

This is the direct source-to-outer-repair bridge.  The full compatibility
matrix selects the speed correction and the same selected Kummer solution.
If the ORIGINAL source size is O(s^(-rho)), the already proved source-to-jet
theorem gives an O(s^(-rho)) upper value/slope.  Feeding exactly that jet
(with the same sign, as the C1 replacement tail) into the physical interface repair gives an
O(s^(-(rho+kappa_phys))) scaled Kummer residual.

No independent boundary-jet decay and no abstract remote solver are assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

theorem actual_Hartree_selected_Kummer_repair_next_source_layer
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B)
    (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C C1 C2 : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
      0 < C ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ (ell c a s beta rhoStar rho Csrc : ℝ),
        (hell : 0 < ell) → ell ≤ 1 →
        let L := actualHartreeSlowInnerRadius ell
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
        1 ≤ s → ell ≤ s ^ (-beta) →
        1 / 2 < beta → 0 < rhoStar →
        rhoStar < (5 * beta - 2) / 4 →
        0 ≤ Csrc →
      ∀ (Fp Fm : ℝ → ℝ)
        (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
        Continuous Fp → Continuous Fm →
      ∀ (F : ℝ → ℂ) (Q Kreg : ℝ), 0 ≤ Q → 0 ≤ Kreg →
        IntervalIntegrable F volume
          (actualHartreeSlowInnerRadius ell / a) B →
        (∀ r ∈ Icc (actualHartreeSlowInnerRadius ell / a) B,
          ‖F r‖ ≤ Q / r ^ 2) →
        ‖originGreenCoeffB K (actualHartreeSlowInnerRadius ell / a) F B‖ ≤
          Kreg * (innerWeightedNorm (7 / 4 : ℝ) Fp +
            innerWeightedNorm (7 / 4 : ℝ) Fm + Q) →
        innerWeightedNorm (7 / 4 : ℝ) Fp +
            innerWeightedNorm (7 / 4 : ℝ) Fm + Q ≤
          Csrc * s ^ (-rho) →
        ∃ p : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K
            (actualHartreeSlowInnerRadius ell) c
            (show 0 < actualHartreeSlowInnerRadius ell by
              unfold actualHartreeSlowInnerRadius
              exact Real.rpow_pos_of_pos hell _)
            a (actualHartreeSlowInnerRadius ell / a) B
            Fp Fm hp hm F p.1 p.2 = 0 ∧
          (∀ q : ℝ × ℝ,
            actualMomentLockedCoupledCompatibility K
              (actualHartreeSlowInnerRadius ell) c
              (show 0 < actualHartreeSlowInnerRadius ell by
                unfold actualHartreeSlowInnerRadius
                exact Real.rpow_pos_of_pos hell _)
              a (actualHartreeSlowInnerRadius ell / a) B
              Fp Fm hp hm F q.1 q.2 = 0 → q = p) ∧
          let L := actualHartreeSlowInnerRadius ell
          let hLp : 0 < L := by
            unfold L actualHartreeSlowInnerRadius
            exact Real.rpow_pos_of_pos hell _
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
          let UB := actualOriginMatchedKummerValue K (L / a) B Fo J.1 J.2 B
          let DUB := actualOriginMatchedKummerSlope K (L / a) B Fo J.1 J.2 B
          let Krep :=
            (9*C2+12*C1+2)/B^2 + 3*C1+1+
              ‖frozenZeroCoeff mu theta‖
          let CJ :=
            actualHartreeSelectedUpperJetBasisConstant D G B *
              (C + Kreg) * Csrc
          ∀ y ∈ Icc (a * B) (2 * a * B),
            ‖actualMatchedScaledKummerApply mu theta a
                (actualKummerPhysicalInterfaceRepair a B UB DUB) y‖ ≤
              (Krep * CJ) *
                s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) := by
  obtain ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, hJetOrder⟩ :=
    actual_Hartree_selected_upper_jet_inherits_source_time_order
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨C1, C2, hC1, hC2, hRepair⟩ :=
    actual_Hartree_Kummer_physical_interface_repair_next_layer
  refine ⟨L0, epsilon, C, C1, C2,
    hL0, heps, hepsOne, hC, hC1, hC2, ?_⟩
  intro ell c a s beta rhoStar rho Csrc hell hellOne
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  have hLp : 0 < L := by
    dsimp [L, actualHartreeSlowInnerRadius]
    exact Real.rpow_pos_of_pos hell _
  intro hLarge ha3 hSmall hs htrap hbeta hrhoStar hflat hCsrc
    Fp Fm hp hm hcp hcm F Q Kreg hQ hKreg hF hEnvelope hBase hSource
  obtain ⟨p, hCompat, hUnique, hJet⟩ :=
    hJetOrder L c a s rho Csrc hLp hLarge ha3 hSmall hs hCsrc
      Fp Fm hp hm hcp hcm F Q Kreg hQ hKreg hF hEnvelope hBase hSource
  refine ⟨p, hCompat, hUnique, ?_⟩
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
  let UB := actualOriginMatchedKummerValue K (L / a) B Fo J.1 J.2 B
  let DUB := actualOriginMatchedKummerSlope K (L / a) B Fo J.1 J.2 B
  let Krep : ℝ :=
    (9*C2+12*C1+2)/B^2 + 3*C1+1+
      ‖frozenZeroCoeff mu theta‖
  let CJ : ℝ :=
    actualHartreeSelectedUpperJetBasisConstant D G B *
      (C + Kreg) * Csrc
  have hJet' : ‖UB‖ + B * ‖DUB‖ ≤ CJ * s ^ (-rho) := by
    dsimp [UB, DUB, J, Fo, S, P, Fpa, Fma, Gp, Gm, CJ]
    simpa only [L, hLp, hpa, hma] using hJet
  have hKrep : 0 ≤ Krep := by
    dsimp [Krep]
    positivity
  have hCJ : 0 ≤ CJ := by
    dsimp [CJ, actualHartreeSelectedUpperJetBasisConstant]
    positivity
  have hkappa : 0 < actualHartreePhysicalKappa beta rhoStar :=
    actual_Hartree_physical_kappa_positive
      beta rhoStar hbeta hrhoStar hflat
  intro y hy
  have hRaw :=
    hRepair mu theta a B y s ell beta rhoStar
      (by
        have hLthree : 0 < L ^ 3 := pow_pos hLp 3
        exact hLthree.trans_le ha3)
      hB hy hs hell hellOne ha3 htrap hbeta hrhoStar hflat
      UB DUB
  dsimp only at hRaw
  have hsp : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hkpow :
      0 ≤ s ^ (-actualHartreePhysicalKappa beta rhoStar) :=
    Real.rpow_nonneg hsp.le _
  have hD :
      Krep * (‖UB‖ + B * ‖DUB‖) ≤
        Krep * (CJ * s ^ (-rho)) :=
    mul_le_mul_of_nonneg_left hJet' hKrep
  have hProd :
      s ^ (-rho) *
          s ^ (-actualHartreePhysicalKappa beta rhoStar) =
        s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) := by
    rw [← Real.rpow_add hsp]
    congr 1
    ring
  calc
    _ ≤ (Krep * (‖UB‖ + B * ‖DUB‖)) *
        s ^ (-actualHartreePhysicalKappa beta rhoStar) := by
      simpa only [Krep] using hRaw
    _ ≤ (Krep * (CJ * s ^ (-rho))) *
        s ^ (-actualHartreePhysicalKappa beta rhoStar) :=
      mul_le_mul_of_nonneg_right hD hkpow
    _ = (Krep * CJ) *
        (s ^ (-rho) *
          s ^ (-actualHartreePhysicalKappa beta rhoStar)) := by ring
    _ = (Krep * CJ) *
        s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) := by
      rw [hProd]

end HBL.TypeIIDynamicSelection
