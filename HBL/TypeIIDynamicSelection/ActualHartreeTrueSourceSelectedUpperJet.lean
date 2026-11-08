import HBL.TypeIIDynamicSelection.ActualHartreeSelectedUpperJet
import HBL.TypeIIDynamicSelection.ActualHartreeKummerRegularTailGain
import HBL.TypeIIDynamicSelection.ActualHartreeOriginOutgoingGain
import Mathlib.Tactic

/-!
# True nonlocal Hartree source selects the UNIQUE compatible Kummer upper jet

The already strictly verified source-to-unique-speed-to-Kummer-upper-jet
theorem required an outer source envelope and a regular-Green norm.
Here both premises are DERIVED for the actual three-Riesz-potential
quartic Hartree source F(r)=-a^2 S_Hartree(ar), not inserted by hand.

The true physical source gives Q=C_phys ell^(1/8), and its regular
origin Green coefficient is bounded by (8/3)G*Q*L^(-3/8).
For L>=6 the last factor is at most 1; therefore the selected original
Fredholm-compatible speed and the SAME forced upper value and slope
are bounded by the actual source norms, without separate upper-jet or
regular Green smallness assumptions.

The physical geometric condition L/a<=B is kept visible. This proves
a fixed-slice source-to-selected-upper-jet theorem. Connecting it to
the true one-orbit time-parameter source derivative and the global
nonlocal PDE residual O(s^(-9/4)) remains open; there is no presupposed
Type-II rate.
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

theorem actual_Hartree_true_nonlocal_source_selected_upper_Kummer_jet
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
      let Kr : ℝ := (8 / 3 : ℝ) * G
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
          (C + Kr) * (N + Q) := by
  obtain ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, hSelect⟩ :=
    actual_Hartree_selected_upper_regular_jet_region
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
  let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let Kr : ℝ := (8 / 3 : ℝ) * G
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
  have hKr : 0 ≤ Kr := by dsimp [Kr]; positivity
  have hN : 0 ≤ N := by
    dsimp [N]
    exact add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
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
  have hRegRaw :=
    actual_Hartree_scaled_Kummer_regular_Green_tail_gain
      K D G L B a Bz Az ell c hD hG hLone ha
      hOrder hBR hcoeff hbound hBz hAz hell hellOne hc
      z hz hSup hStrauss
  have hPow : L ^ (-(3 / 8 : ℝ)) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hLone
        (by norm_num : -(3 / 8 : ℝ) ≤ 0))
  have hBase :
      ‖originGreenCoeffB K (L / a) F B‖ ≤ Kr * (N + Q) := by
    calc
      _ ≤ (Kr * Q) * L ^ (-(3 / 8 : ℝ)) := by
        simpa only [Kr, Q, F, mul_assoc] using hRegRaw
      _ ≤ Kr * Q := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hPow (mul_nonneg hKr hQ))
      _ ≤ Kr * (N + Q) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hN) hKr
  obtain ⟨p, hCompat, hUnique, hJet⟩ :=
    hSelect L c a hLp hLarge ha3 hSmall
      Fp Fm hp hm hcp hcm F Q Kr hQ hKr hFI hEnvelope hBase
  exact ⟨p, hCompat, hUnique, hJet⟩

end HBL.TypeIIDynamicSelection
