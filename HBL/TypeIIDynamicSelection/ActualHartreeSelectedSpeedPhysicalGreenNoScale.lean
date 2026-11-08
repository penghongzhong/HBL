import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSpeedSelection
import HBL.TypeIIDynamicSelection.ActualHartreeSelectedSpeedSingularGreenGain
import Mathlib.Tactic

/-!
# True Hartree Riesz source, UNIQUE selected speed and its physical Green bound

The earlier source-to-selected-speed theorem already constructs a unique
real two-speed pair p from the original complete quartic Hartree source
F0=-a^2 S_Hartree(a*r). Its actual size is
  |p.1|+|p.2| <= C/a * (N_Fredholm + Cphys*ell^(1/8)).
The genuine two speed source directions have only a 1/r outer tail.
The original Kummer Wronskian proof gives a positive factor a in the
ACTUAL physical product Y(r) * integral(speed source/W), compensating
the factor 1/a in the selected speed bound.

Here both producers are connected with the SAME selected p, original
Hartree source and actual physical Green basis. The final bound loses
NO moving scale a. No arbitrary forcing, separate speed hypothesis,
unproved physical profile, or prespecified Type-II rate enters.

This is a load-bearing fixed-slice source correction bound. The
differentiable one-orbit path, exact nonlocal full-field residual
O(s^(-9/4)) and direct threshold Lipschitz remain open.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

theorem actual_Hartree_original_source_selected_speed_Green_no_scale_loss
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
        ∀ r ∈ Icc (L / a) B,
          let Fsp : ℝ → ℂ := fun x =>
            (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
            (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
          ‖originPhysicalValue K.y r *
            originGreenCoeffA K r Fsp (L / a)‖ ≤
            (G ^ 2 * Cs * C) * (N + Q) := by
  obtain ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, hSelect⟩ :=
    actual_Hartree_true_nonlocal_source_selects_unique_real_speed
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨Cs, hCs, hPhysical⟩ :=
    actual_Hartree_speed_correction_singular_Green_no_scale_loss
  refine ⟨L0, epsilon, C, Cs, hL0, heps, hepsOne, hC, hCs, ?_⟩
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
  intro r hr
  let Fsp : ℝ → ℂ := fun x =>
    (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
    (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
  have hLone : 1 ≤ L := by linarith
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
  have hPhysicalRaw :=
    hPhysical K G L c a B hG hLone ha hBOne hBR
      hSmallOne hOrder hbound p r hr
  have hActual :
      ‖originPhysicalValue K.y r * originGreenCoeffA K r Fsp (L / a)‖ ≤
        G ^ 2 * Cs * a * (|p.1| + |p.2|) := by
    simpa only [Fsp] using hPhysicalRaw
  have hCoef : 0 ≤ G ^ 2 * Cs * a := by positivity
  calc
    ‖originPhysicalValue K.y r * originGreenCoeffA K r Fsp (L / a)‖ ≤
        G ^ 2 * Cs * a * (|p.1| + |p.2|) := hActual
    _ ≤ G ^ 2 * Cs * a * ((C / a) * (N + Q)) :=
      mul_le_mul_of_nonneg_left hSize hCoef
    _ = (G ^ 2 * Cs * C) * (N + Q) := by
      field_simp [ha.ne']
      ring

end HBL.TypeIIDynamicSelection
