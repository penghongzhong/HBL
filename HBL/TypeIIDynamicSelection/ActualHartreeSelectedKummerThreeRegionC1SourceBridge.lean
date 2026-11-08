import HBL.TypeIIDynamicSelection.ActualHartreeSelectedKummerRepairSourceTimeGain
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalKummerC1PDEH1
import HBL.TypeIIDynamicSelection.ActualHartreeAdjustedKummerSourceContinuity
import Mathlib.Tactic

/-!
# One source-selected Hartree Kummer field: physical C1, equations, and energy

The same actual Hartree weighted source selects exactly one real compatibility
speed, one complete adjusted forcing Fo, one normalized Green solution, and
its actual right jet. This single source-selected object simultaneously
satisfies the pointwise positive-time bubble bound, physical C1 matching
at both joins, exact frozen scaled Kummer equations in all three open
regions, and positive radial Hdot1 shell energy gain.

Continuity of the adjusted forcing follows from the original source F
and the genuine monopole speed directions. No new regularity assumption
is imposed on the adjusted source, selected jet, or remote trace. This does NOT solve the global nonlinear
three-region Hartree PDE or the order 9/4 parametrix problem.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

theorem actual_Hartree_selected_source_Kummer_three_region_C1_PDE_and_H1
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
      ∀ (L c a s rho delta Csrc Cq beta : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
        1 ≤ s → 0 ≤ Csrc → 0 ≤ Cq →
        a ^ 2 ≤ Cq * s → 0 < delta →
        1 / 2 + delta ≤ rho → 1 / 2 < beta → L ≤ a * B →
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
        innerWeightedNorm (7 / 4 : ℝ) Fp +
            innerWeightedNorm (7 / 4 : ℝ) Fm + Q ≤
          Csrc * s ^ (-rho) →
        (∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r) →
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
          let UB := actualOriginMatchedKummerValue K (L / a) B Fo J.1 J.2 B
          let DUB := actualOriginMatchedKummerSlope K (L / a) B Fo J.1 J.2 B
          let CD := actualHartreeSelectedUpperJetBasisConstant D G B *
            (C + Kreg) * Csrc
          let v := actualOriginMatchedKummerPullback K a (L / a) B Fo J.1 J.2
          let repair := actualKummerPhysicalInterfaceRepair a B UB DUB
          let glued := actualPhysicalMatchedKummerC1Splice a B v repair
          (‖UB‖ + B * ‖DUB‖ ≤ CD * s ^ (-rho)) ∧
          (∀ y : ℝ, 0 < y →
            ‖actualKummerPhysicalOuterRepair
                (fun _ : ℝ => a) B (fun _ : ℝ => UB)
                (fun _ : ℝ => DUB) s y‖ ≤
              ((1 + 2 * Real.sqrt Cq) * CD) *
                s ^ (-delta) * bubble y) ∧
          HasDerivAt glued ((1 / a : ℝ) • DUB) (a * B) ∧
          HasDerivAt glued 0 (2 * a * B) ∧
          (∀ y ∈ Ioo 0 (a * B),
            actualMatchedScaledKummerApply mu theta a glued y =
              ((a ^ 2)⁻¹ : ℝ) • Fo (y / a)) ∧
          (∀ y ∈ Ioo (a * B) (2 * a * B),
            actualMatchedScaledKummerApply mu theta a glued y =
              actualMatchedScaledKummerApply mu theta a repair y) ∧
          (∀ y : ℝ, 2 * a * B < y →
            actualMatchedScaledKummerApply mu theta a glued y = 0) ∧
          ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
            (∫ y in Icc (a * B) (2 * a * B),
              y ^ 2 * ‖deriv repair y‖ ^ 2) ≤
                (4 * (3 * C1 + 1) ^ 2 *
                  Real.sqrt Cq * CD ^ 2) *
                  s ^ (-actualKummerRepairCenterTimeGain beta) := by
  obtain ⟨L0, eps, C, hLarge0, heps, heps1, hC, hSelected⟩ :=
    actual_Hartree_selected_physical_Kummer_repair_from_source_order
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, eps, C, hLarge0, heps, heps1, hC, ?_⟩
  intro L c a s rho delta Csrc Cq beta hLp hLarge ha3 hSmall hs
    hCsrc hCq hClock hdelta hRho hBeta hXlow
    Fp Fm hp hm hcp hcm F Q Kreg hQ hKreg hF hEnvelope hBase
    hSource hFcont
  obtain ⟨p, hCompat, hUnique, hSelectedRest⟩ :=
    hSelected L c a s rho delta Csrc Cq hLp hLarge ha3 hSmall hs
      hCsrc hCq hClock hdelta hRho
      Fp Fm hp hm hcp hcm F Q Kreg hQ hKreg
      hF hEnvelope hBase hSource
  refine ⟨p, hCompat, hUnique, ?_⟩
  dsimp only at hSelectedRest ⊢
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
  let CD := actualHartreeSelectedUpperJetBasisConstant D G B *
    (C + Kreg) * Csrc
  let v := actualOriginMatchedKummerPullback K a (L / a) B Fo J.1 J.2
  let repair := actualKummerPhysicalInterfaceRepair a B UB DUB
  let glued := actualPhysicalMatchedKummerC1Splice a B v repair
  obtain ⟨hJet, hBubble⟩ := hSelectedRest
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hr0 : 0 < L / a := div_pos hLp ha
  have hLB : L / a ≤ B := (div_le_iff₀ ha).2 (by
    simpa only [mul_comm] using hXlow)
  have hFo : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt Fo r := by
    intro r hr
    change ContinuousAt (fun x : ℝ =>
      F x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
        (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x) r
    exact actual_Hartree_adjusted_Kummer_source_continuousAt
      a c r ha hr.1 F (hFcont r hr) p
  have hCX : 0 ≤ Real.sqrt Cq := Real.sqrt_nonneg _
  have hRadius : a * B ≤ Real.sqrt Cq * s ^ (1 / 2 : ℝ) :=
    actual_Kummer_repair_radius_sqrt_from_clock
      a B (a ^ 2) s Cq ha.le hBOne hs hCq rfl hClock
  have hCD : 0 ≤ CD := by
    dsimp [CD]
    have hBasis : 0 ≤ actualHartreeSelectedUpperJetBasisConstant D G B := by
      dsimp [actualHartreeSelectedUpperJetBasisConstant]
      positivity
    exact mul_nonneg (mul_nonneg hBasis (add_nonneg hC.le hKreg)) hCsrc
  have hRhoH1 :
      (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho := by
    have hk : actualKummerRepairCenterTimeGain beta ≤ 1 / 2 := by
      unfold actualKummerRepairCenterTimeGain
      exact min_le_right _ _
    linarith
  obtain ⟨C1, C2, hC1, hC2, hCert⟩ :=
    actual_Hartree_physical_matched_Kummer_C1_PDE_and_H1_certificate
      K a s beta rho (Real.sqrt Cq) CD ha hr0 hLB hBR
      hs hBeta hRhoH1 hCX hCD hRadius Fo hFo J.1 J.2 hJet
  have hRegions :=
    actual_Hartree_physical_Kummer_C1Splice_three_source_regions
      K a ha hr0 hLB hBR Fo hFo J.1 J.2
  dsimp only at hCert hRegions
  refine ⟨hJet, hBubble, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hCert.2.1
  · exact hCert.2.2.1
  · exact hRegions.1
  · exact hRegions.2.1
  · exact hRegions.2.2
  · exact ⟨C1, C2, hC1, hC2, hCert.2.2.2⟩

end HBL.TypeIIDynamicSelection
