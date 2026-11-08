import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSpeedSelection
import HBL.TypeIIDynamicSelection.ActualHartreeKummerSingularGreenCompatibilityTransport
import Mathlib.Tactic

/-!
# Genuine Hartree source and UNIQUE selected speed give compatible Green transport

Earlier physical estimates for the singular origin Green branch stated the
exact complex compatibility condition on a supplied outer forcing. It is
NOT correct to impose that condition on the unadjusted core-radiation source.

This theorem derives the unique real two-speed p from the ORIGINAL complete
nonlocal Hartree Riesz source. It then constructs the associated physical
corrected Fredholm inner sources and the genuinely adjusted Kummer forcing
Fo = F0 - p_b*S_b - p_omega*S_omega. Both actual speed source terms are
integrable on the matching annulus; the literal compatibility obstruction
for the adjusted Fo is *derived* from the selected p.

The exact singular Green moment transport then applies to the SAME adjusted
Fo and SAME corrected left Fredholm jet. No arbitrary hzero compatibility
hypothesis on F0, no free singular amplitude and no assumed blowup rate.

This is still a fixed physical time slice. A differentiable parameter path,
uniform full nonlinear Hartree PDE residual s^(-9/4), and threshold
Lipschitz control are not consequences of this theorem.
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

theorem actual_Hartree_true_source_unique_speed_selected_Green_transport
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
      let F0 : ℝ → ℂ :=
        fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
      let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
        ell ^ (1 / 8 : ℝ)
      let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm
      ∃ p : ℝ × ℝ,
        actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
          Fp Fm hp hm F0 p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
        (|p.1| + |p.2| ≤ (C / a) * (N + Q)) ∧
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
        let Fo := fun r => F0 r + (-(p.1 : ℂ)) * S r + (-(p.2 : ℂ)) * P r
        let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
        ∀ r ∈ Icc (L / a) B,
          originGreenCoeffA K B Fo r =
            actualOriginOutgoingTrace K (L / a) J.1 J.2 -
              ∫ x in (L / a)..r, originGreenSourceA K Fo x := by
  obtain ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, hSelect⟩ :=
    actual_Hartree_true_nonlocal_source_selects_unique_real_speed
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss
  dsimp only
  let F0 : ℝ → ℂ :=
    fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
  let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
    ell ^ (1 / 8 : ℝ)
  let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  obtain ⟨p, hCompat, hUnique, hSize⟩ :=
    hSelect L c a hLp hLarge ha3 hSmall hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  refine ⟨p, hCompat, hUnique, hSize, ?_⟩
  dsimp only
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
  let Fo := fun r => F0 r + (-(p.1 : ℂ)) * S r + (-(p.2 : ℂ)) * P r
  let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hr0 : 0 < L / a := div_pos hLp ha
  have hLone : 1 ≤ L := by linarith
  have haOne : 1 ≤ a := (one_le_pow₀ hLone).trans ha3
  have hc : |c| ≤ 1 := by
    have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
    have hca : |c| ≤ a * |c| := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right haOne (abs_nonneg c))
    exact hca.trans hSmallOne
  have hFI : IntervalIntegrable F0 volume (L / a) B :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable
      Bz Az ell c a (L / a) B hBz hAz hell hellOne hc
      ha hr0 hOrder z hz hSup hStrauss).neg
  have hS :=
    actual_Hartree_moment_locked_scaled_speed_integrable_on
      a c (L / a) B ha hr0 hOrder
  have hFoInt : IntervalIntegrable Fo volume (L / a) B := by
    dsimp [Fo]
    exact (hFI.add (hS.1.const_mul (-(p.1 : ℂ)))).add
      (hS.2.const_mul (-(p.2 : ℂ)))
  have hCompatOb :
      actualMomentLockedIntervalObstruction K (L / a) B Fo J.1 J.2 = 0 := by
    have hFoEq : Fo = (fun r => F0 r -
      (p.1 : ℂ) * S r - (p.2 : ℂ) * P r) := by
      funext r
      dsimp [Fo]
      ring
    rw [hFoEq]
    change actualMomentLockedIntervalObstruction K (L / a) B
      (fun r => F0 r - (p.1 : ℂ) * S r -
        (p.2 : ℂ) * P r) J.1 J.2 = 0 at hCompat
    exact hCompat
  let Cbasis : ℝ :=
    G * (1 / (L / a) + 1 / (L / a) ^ 2) + B ^ 2 + 1
  have hK : OriginBasisOn K (L / a) B Cbasis :=
    origin_kummer_annulus_bound K (L / a) B G hr0 hBR hG hbound
  intro r hr
  exact actual_Hartree_compatible_singular_Green_coefficient_local_transport
    K (L / a) B Cbasis hK hOrder Fo hFoInt J.1 J.2 hCompatOb r hr

end HBL.TypeIIDynamicSelection
