import HBL.TypeIIDynamicSelection.ActualHartreeSelectedSpeedPhysicalGreenNoScale
import HBL.TypeIIDynamicSelection.ActualHartreeSingularGreenPhysicalSourceGain
import HBL.TypeIIDynamicSelection.ActualOriginGreenIntegrable
import Mathlib.Tactic

/-!
# The genuinely adjusted Hartree source: scale-free singular Green product

Both the complete inverse-square quartic Hartree interaction F0 and its two
genuine selected-speed corrections enter ONE Kummer source Fo.
The original local physical Green product has a scale-free bound proportional
to the physical ell^(1/8) interaction norm. The selected-speed correction has
a scale-free bound after the unique compatibility selector. Here linearity of
the actual interval Green integral is proved using the original normalized
Kummer basis and the two actual integrability certificates, and the two
bounds are combined for the SAME real selected speed.

This is the full adjusted LOCAL Green integral, not yet the transported
right-endpoint coefficient or the time-dependent nonlinear PDE residual.
No Type-II speed is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

private theorem actual_origin_Green_A_source_add_on
    {mu theta scale r0 r Cbasis : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hBasis : OriginBasisOn K r0 r Cbasis) (hOrder : r0 ≤ r)
    (F H : ℝ → ℂ)
    (hF : IntervalIntegrable F volume r0 r)
    (hH : IntervalIntegrable H volume r0 r) :
    originGreenCoeffA K r (fun x => F x + H x) r0 =
      originGreenCoeffA K r F r0 + originGreenCoeffA K r H r0 := by
  have hFI := (actual_origin_Green_source_integrability K hBasis hOrder F hF).1
  have hHI := (actual_origin_Green_source_integrability K hBasis hOrder H hH).1
  have hSource : originGreenSourceA K (fun x => F x + H x) =
      (fun x => originGreenSourceA K F x + originGreenSourceA K H x) := by
    funext x
    unfold originGreenSourceA
    ring
  unfold originGreenCoeffA
  rw [hSource, intervalIntegral.integral_add hFI hHI]

theorem actual_Hartree_true_source_selected_adjusted_local_Green_no_scale_loss
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧
        ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C Cs : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
      0 < C ∧ 0 < Cs ∧
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
      ∃ p : ℝ × ℝ,
        actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
          Fp Fm hp hm F0 p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
        (|p.1| + |p.2| ≤ (C / a) * (N + Q)) ∧
        ∀ r ∈ Icc (L / a) B,
          let Fo : ℝ → ℂ := fun x =>
            F0 x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
              (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
          ‖originPhysicalValue K.y r *
            originGreenCoeffA K r Fo (L / a)‖ ≤
            G * (1 + (D + 1) * G * B ^ 2) * Q +
              (G ^ 2 * Cs * C) * (N + Q) := by
  obtain ⟨L0, epsilon, C, Cs, hL0, heps, hepsOne, hC, hCs, hSelect⟩ :=
    actual_Hartree_original_source_selected_speed_Green_no_scale_loss
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, C, Cs, hL0, heps, hepsOne, hC, hCs, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss
  dsimp only
  let F0 : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let Q : ℝ :=
    actualHartreePhysicalWeightedSourceConstant Bz Az * ell ^ (1 / 8 : ℝ)
  let N : ℝ :=
    innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  obtain ⟨p, hCompat, hUnique, hSize, hSpeedLocal⟩ :=
    hSelect L c a hLp hLarge ha3 hSmall hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  refine ⟨p, hCompat, hUnique, hSize, ?_⟩
  intro r hr
  dsimp only
  let Fsp : ℝ → ℂ := fun x =>
    (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
      (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
  let Fo : ℝ → ℂ := fun x =>
    F0 x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
      (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
  have hLone : 1 ≤ L := by linarith
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have haOne : 1 ≤ a := (one_le_pow₀ hLone).trans ha3
  have hc : |c| ≤ 1 := by
    have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
    have hca : |c| ≤ a * |c| := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right haOne (abs_nonneg c))
    exact hca.trans hSmallOne
  have hr0 : 0 < L / a := div_pos hLp ha
  have hOriginalRaw :=
    actual_Hartree_singular_Green_local_moment_full_product_gain
      K D G L B a Bz Az ell c hD hG hLone ha hOrder
      hBR hcoeff hbound hBz hAz hell hellOne hc z hz hSup hStrauss r hr
  have hOriginal :
      ‖originPhysicalValue K.y r *
        originGreenCoeffA K r F0 (L / a)‖ ≤
        G * (1 + (D + 1) * G * B ^ 2) * Q := by
    simpa only [F0, Q] using hOriginalRaw.2
  have hSpeed :
      ‖originPhysicalValue K.y r *
        originGreenCoeffA K r Fsp (L / a)‖ ≤
        (G ^ 2 * Cs * C) * (N + Q) := by
    simpa only [Fsp] using hSpeedLocal r hr
  have hFI : IntervalIntegrable F0 volume (L / a) r :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable
      Bz Az ell c a (L / a) r hBz hAz hell hellOne hc ha
      hr0 hr.1 z hz hSup hStrauss).neg
  have hSources :=
    actual_Hartree_moment_locked_scaled_speed_integrable_on
      a c (L / a) r ha hr0 hr.1
  have hFsp : IntervalIntegrable Fsp volume (L / a) r := by
    dsimp [Fsp]
    exact (hSources.1.const_mul (-(p.1 : ℂ))).add
      (hSources.2.const_mul (-(p.2 : ℂ)))
  let Cbasis : ℝ :=
    G * (1 / (L / a) + 1 / (L / a) ^ 2) + r ^ 2 + 1
  have hBasis : OriginBasisOn K (L / a) r Cbasis :=
    origin_kummer_annulus_bound K (L / a) r G hr0
      (hr.2.trans_lt hBR) hG hbound
  have hAdd :=
    actual_origin_Green_A_source_add_on K hBasis hr.1 F0 Fsp hFI hFsp
  have hFoEq : Fo = (fun x => F0 x + Fsp x) := by
    funext x
    dsimp [Fo, Fsp]
    ring
  calc
    ‖originPhysicalValue K.y r *
        originGreenCoeffA K r Fo (L / a)‖ =
      ‖originPhysicalValue K.y r *
          originGreenCoeffA K r F0 (L / a) +
        originPhysicalValue K.y r *
          originGreenCoeffA K r Fsp (L / a)‖ := by
          rw [hFoEq, hAdd, mul_add]
    _ ≤ ‖originPhysicalValue K.y r *
          originGreenCoeffA K r F0 (L / a)‖ +
        ‖originPhysicalValue K.y r *
          originGreenCoeffA K r Fsp (L / a)‖ := norm_add_le _ _
    _ ≤ G * (1 + (D + 1) * G * B ^ 2) * Q +
        (G ^ 2 * Cs * C) * (N + Q) := add_le_add hOriginal hSpeed

end HBL.TypeIIDynamicSelection
