import HBL.TypeIIDynamicSelection.ActualHartreeSelectedSpeedBound
import HBL.TypeIIDynamicSelection.ActualHartreeOriginOutgoingGain
import Mathlib.Tactic

/-!
# Genuine nonlocal Hartree source selects unique two-channel real speed

We instantiate the previously strictly verified unique Cramer selector
with the ORIGINAL physical inverse-square quartic Hartree source:
  F(r) = -a^2 * PhysicalHartreeInteraction(ell,c,z)(a*r).

Neither `IntervalIntegrable F` nor `|F(r)|<=Q/r²` is inserted as a
separate premise: the physical three-Riesz-potential source producer
proves both from measurability, the actual Strauss radiation bounds,
and the genuine ell^(1/8) spatial estimate. In particular Q is the
original explicit physical Hartree constant, not an abstract symbol.

Consequently the unique compatible real modulation speed and its
quantitative bound follow from the original physical source on each
valid annular slice. The geometric condition L/a<=B is explicit;
it is not a blowup-rate condition. Constructing this selector as
one differentiable time-dependent parameter path, and the fixed
s^(-9/4) full nonlinear PDE source recursion, remain open.
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

theorem actual_Hartree_true_nonlocal_source_selects_unique_real_speed
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
      let F : ℝ → ℂ :=
        fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
      let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
        ell ^ (1 / 8 : ℝ)
      let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm
      ∃ p : ℝ × ℝ,
        actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
          Fp Fm hp hm F p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F q.1 q.2 = 0 → q = p) ∧
        |p.1| + |p.2| ≤ (C / a) * (N + Q) := by
  obtain ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, hSelect⟩ :=
    actual_Hartree_selected_speed_original_bound_region
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss
  dsimp only
  let F : ℝ → ℂ :=
    fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
  let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
    ell ^ (1 / 8 : ℝ)
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hLone : 1 ≤ L := by linarith
  have haOne : 1 ≤ a := (one_le_pow₀ hLone).trans ha3
  have hc : |c| ≤ 1 := by
    have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
    have hca : |c| ≤ a * |c| := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right haOne (abs_nonneg c))
    exact hca.trans hSmallOne
  have hr0 : 0 < L / a := div_pos hLp ha
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg
      (actualHartreePhysicalWeightedSourceConstant_nonneg Bz Az hBz hAz)
      (Real.rpow_nonneg hell.le _)
  have hFI : IntervalIntegrable F volume (L / a) B :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable
      Bz Az ell c a (L / a) B hBz hAz hell hellOne hc
      ha hr0 hOrder z hz hSup hStrauss).neg
  have hEnvelope : ∀ r ∈ Icc (L / a) B,
      ‖F r‖ ≤ Q / r ^ 2 := by
    intro r hr
    have hrp : 0 < r := hr0.trans_le hr.1
    have h :=
      actual_Hartree_scaled_Kummer_source_annulus_bound
        Bz Az ell c a r r hBz hAz hell hellOne hc
        ha hrp le_rfl z hz hSup hStrauss
    simpa only [F, Q, norm_neg] using h
  obtain ⟨p, hCompat, hUnique, hSize⟩ :=
    hSelect L c a hLp hLarge ha3 hSmall
      Fp Fm hp hm hcp hcm F Q hQ hFI hEnvelope
  exact ⟨p, hCompat, hUnique, hSize⟩

end HBL.TypeIIDynamicSelection
