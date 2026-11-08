import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedFullSingularOriginalNorm
import HBL.TypeIIDynamicSelection.ActualHartreeSinglePhysicalSourceTwoChannelSelection
import Mathlib.Tactic

/-!
# ONE original nonlocal 3D Hartree source supplies ALL selected singular Green channels

The real and imaginary Fredholm transmission sources are not free forcing
functions: they are the two genuine weighted channels of the same complete
inverse-square quartic Hartree Riesz interaction with radiation z.
The original outer Kummer source is its true scaled pullback.
The existing physical source theorem derives both inner weighted L2
certificates directly from the 1/16 weighted slow-inner Hartree estimate.
The uniquely selected real two-speed is used to construct one corrected
outer Kummer forcing, and the full outgoing singular physical Green field
is controlled solely by the ORIGINAL physical inner norm and ell^(1/8)
source norm, with no positive factor of moving Kummer scale a.

Continuity of both original transmission channels is an EXPLICIT premise:
measurable z and weighted L2 membership do not imply continuity.
This is a fixed-slice original-PDE-source statement, NOT yet a
time-differentiable orbit, all-four-piece residual or the Type-II rate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_one_physical_source_selected_full_singular_Green_gain
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
      ∀ (Bz Az ell c a : ℝ) (hell : 0 < ell),
        0 ≤ Bz → 0 ≤ Az → ell ≤ 1 →
        L0 ≤ actualHartreeSlowInnerRadius ell →
        (actualHartreeSlowInnerRadius ell) ^ 3 ≤ a →
        a * |c| ≤ epsilon →
        actualHartreeSlowInnerRadius ell / a ≤ B →
      ∀ (z : ℝ → ℂ), Measurable z →
        (∀ y : ℝ, 0 < y → ‖z y‖ ≤ Bz) →
        (∀ y : ℝ, 1 ≤ y → y * ‖z y‖ ≤ Az) →
        Continuous (actualHartreeTransmissionPlusSource ell c z) →
        Continuous (actualHartreeTransmissionMinusSource ell c z) →
      let L := actualHartreeSlowInnerRadius ell
      let hL : 0 < L := Real.rpow_pos_of_pos hell _
      let Fp := actualHartreeTransmissionPlusSource ell c z
      let Fm := actualHartreeTransmissionMinusSource ell c z
      let F0 : ℝ → ℂ :=
        fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
      let Q : ℝ :=
        actualHartreePhysicalWeightedSourceConstant Bz Az * ell ^ (1 / 8 : ℝ)
      let N : ℝ :=
        innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm
      let Cr : ℝ := 1 + (D + 1) * G * (B ^ 2 + 2)
      let Cp : ℝ := 1 + (D + 1) * G * B ^ 2
      let Cf : ℝ :=
        actualInnerShellValueConstant + actualInnerShellDerivativeConstant
      ∃ (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
        (p : ℝ × ℝ),
        actualMomentLockedCoupledCompatibility K L c hL a (L / a) B
          Fp Fm hp hm F0 p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hL a (L / a) B
            Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
        ∀ r ∈ Icc (L / a) B,
          let Fo : ℝ → ℂ := fun x =>
            F0 x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
              (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
          ‖originPhysicalValue K.y r * originGreenCoeffA K B Fo r‖ ≤
            (G * Cr * Cf * Cn + G * Cp + G ^ 2 * Cs * C) * (N + Q) := by
  obtain ⟨L0, epsilon, C, Cs, Cn,
      hL0, heps, hepsOne, hC, hCs, hCn, hFull⟩ :=
    actual_Hartree_true_source_selected_full_singular_original_norm_gain
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, C, Cs, Cn,
    hL0, heps, hepsOne, hC, hCs, hCn, ?_⟩
  intro Bz Az ell c a hell hBz hAz hellOne
    hLarge ha3 hSmall hOrder z hz hSup hStrauss hcp hcm
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  let Fp := actualHartreeTransmissionPlusSource ell c z
  let Fm := actualHartreeTransmissionMinusSource ell c z
  have hLp : 0 < L := Real.rpow_pos_of_pos hell _
  have hLone : 1 ≤ L := by linarith [hL0.trans hLarge]
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have haOne : 1 ≤ a := (one_le_pow₀ hLone).trans ha3
  have hc : |c| ≤ 1 := by
    have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
    have hca : |c| ≤ a * |c| := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right haOne (abs_nonneg c))
    exact hca.trans hSmallOne
  have hSource :=
    actual_Hartree_conjugated_slow_inner_one_sixteenth
      ell c Bz Az hell hellOne hc hBz hAz z hz hSup hStrauss
  have hPair :=
    actual_Hartree_one_complex_weighted_source_two_channels
      (7 / 4 : ℝ) _ hSource.1 hSource.2.1
  obtain ⟨p, hCompat, hUnique, hField⟩ :=
    hFull L c a hLp hLarge ha3 hSmall hOrder
      Fp Fm hPair.1 hPair.2 hcp hcm
      Bz Az ell hBz hAz hell hellOne z hz hSup hStrauss
  exact ⟨hPair.1, hPair.2, p, hCompat, hUnique, hField⟩

end HBL.TypeIIDynamicSelection
