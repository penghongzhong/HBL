import HBL.TypeIIDynamicSelection.ActualHartreeSelectedUpperKummerJet
import Mathlib.Tactic

/-!
# Selected compatible Kummer upper jet inherits the current source time order

The selected upper-jet theorem already constructs the unique real speed
correction and controls the actual upper value/slope by the ORIGINAL source
size N0+Q.  This file adds only the time-order propagation:
  N0+Q <= Csrc s^(-rho)
implies the SAME selected upper Kummer jet is O(s^(-rho)).

No boundary-jet order is assumed independently.  This is the producer needed
by the physical Kummer repair next-layer theorem.
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

theorem actual_Hartree_selected_upper_jet_inherits_source_time_order
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
      ∀ (L c a s rho Csrc : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
        1 ≤ s → 0 ≤ Csrc →
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
          (actualHartreeSelectedUpperJetBasisConstant D G B *
            (C + Kreg) * Csrc) * s ^ (-rho) := by
  obtain ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, hSelected⟩ :=
    actual_Hartree_selected_upper_regular_jet_region
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, ?_⟩
  intro L c a s rho Csrc hLp hLarge ha3 hSmall hs hCsrc
    Fp Fm hp hm hcp hcm F Q Kreg hQ hKreg hF hEnvelope hBase hSource
  obtain ⟨p, hCompat, hUnique, hJet⟩ :=
    hSelected L c a hLp hLarge ha3 hSmall
      Fp Fm hp hm hcp hcm F Q Kreg hQ hKreg hF hEnvelope hBase
  refine ⟨p, hCompat, hUnique, ?_⟩
  dsimp only at hJet ⊢
  have hBasis :
      0 ≤ actualHartreeSelectedUpperJetBasisConstant D G B := by
    dsimp [actualHartreeSelectedUpperJetBasisConstant]
    positivity
  have hCoef :
      0 ≤ actualHartreeSelectedUpperJetBasisConstant D G B * (C + Kreg) :=
    mul_nonneg hBasis (add_nonneg hC.le hKreg)
  calc
    _ ≤ actualHartreeSelectedUpperJetBasisConstant D G B * (C + Kreg) *
        (innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm + Q) := hJet
    _ ≤ actualHartreeSelectedUpperJetBasisConstant D G B * (C + Kreg) *
        (Csrc * s ^ (-rho)) :=
      mul_le_mul_of_nonneg_left hSource hCoef
    _ = (actualHartreeSelectedUpperJetBasisConstant D G B *
          (C + Kreg) * Csrc) * s ^ (-rho) := by ring

end HBL.TypeIIDynamicSelection
