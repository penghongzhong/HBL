import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSpeedSelection
import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedLocalizedInner
import HBL.TypeIIDynamicSelection.ActualOneLayerSingleComplexWeightedSource
import Mathlib.Tactic

/-!
# One ORIGINAL Hartree PDE interaction produces BOTH inner Fredholm
# channels and the outer Kummer forcing for its unique real speed

The previously verified source selector was instantiated with the original
outer Hartree forcing, but its real inner Fredholm inputs were generic.
Here the two inner channels are literally the real and imaginary parts
of the SAME original conjugated and localized Hartree nonlocal source
  r*chi_inner(r) * PhysicalHartreeInteraction(ell,c,z)(r).
Their weighted L² membership is derived from the full real three-Riesz
source and the accepted 1/16 slow-inner weighted theorem, not assumed.

The outer Kummer source is the original physical -a² pullback
of that SAME Hartree interaction. The selected speed is unique and
satisfies the exact coupled compatibility equation with those two
physical inner channels, and the original full source bound.

Continuity of the two actual inner channel sources is kept as a
SEPARATE explicit regularity premise here: weighted membership plus
mere measurability does not imply continuity. Deriving this regularity
along one differentiable physical modulation orbit, together with the
time-dependent full Hartree residual O(s^(-9/4)), remains open.
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

theorem actual_Hartree_single_physical_source_selected_two_channel_speed
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧
        ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < C ∧
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
      let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
        ell ^ (1 / 8 : ℝ)
      ∃ (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
        (p : ℝ × ℝ),
        actualMomentLockedCoupledCompatibility K L c hL a (L / a) B
          Fp Fm hp hm F0 p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hL a (L / a) B
            Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
        |p.1| + |p.2| ≤ (C / a) *
          (innerWeightedNorm (7 / 4 : ℝ) Fp +
            innerWeightedNorm (7 / 4 : ℝ) Fm + Q) := by
  obtain ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, hSelect⟩ :=
    actual_Hartree_true_nonlocal_source_selects_unique_real_speed
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, ?_⟩
  intro Bz Az ell c a hell hBz hAz hellOne
    hLarge ha3 hSmall hOrder z hz hSup hStrauss hcp hcm
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  let Fp := actualHartreeTransmissionPlusSource ell c z
  let Fm := actualHartreeTransmissionMinusSource ell c z
  let F0 : ℝ → ℂ :=
    fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
  let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
    ell ^ (1 / 8 : ℝ)
  have hLp : 0 < L := Real.rpow_pos_of_pos hell _
  have hOne : 1 ≤ L := by linarith
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have haOne : 1 ≤ a := (one_le_pow₀ hOne).trans ha3
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
  obtain ⟨p, hCompat, hUnique, hSize⟩ :=
    hSelect L c a hLp hLarge ha3 hSmall hOrder
      Fp Fm hPair.1 hPair.2 hcp hcm
      Bz Az ell hBz hAz hell hellOne z hz hSup hStrauss
  exact ⟨hPair.1, hPair.2, p, hCompat, hUnique, hSize⟩

end HBL.TypeIIDynamicSelection
