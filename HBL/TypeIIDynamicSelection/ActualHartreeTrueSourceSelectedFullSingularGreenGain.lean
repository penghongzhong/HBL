import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedAdjustedLocalGreenNoScale
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedGreenTransport
import HBL.TypeIIDynamicSelection.ActualHartreeFredholmOutgoingNoRadiusLoss
import Mathlib.Tactic

/-!
# The actual selected compatible full singular Green channel

This combines three original-source producers without changing the selected
real two-channel speed:
(1) the genuine complete inverse-square quartic Hartree Riesz source and
    its compatible uniquely selected speed;
(2) the full adjusted local origin Green source integral and its scale-free
    physical Y(r)-product bound;
(3) the exact compatible outgoing transport from the Fredholm Cauchy jet,
    whose true origin-Wronskian projection carries the matching factor r0.

The proof identifies the selector in (1)-(3) by its actual uniqueness
equation. The outgoing coefficient is controlled by the TRUE corrected
Fredholm inner source norm and original Hartree ell^(1/8) norm, without
introducing a positive moving scale a or inverse matching radius.
The still-open part is the full time-dependent nonlinear Hartree residual,
including physical moving-interface and all nonlocal cross interactions.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_true_source_selected_full_singular_Green_physical_no_scale_loss
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
        let Gp := actualMomentLockedInnerPhaseSource L c
        let Gm := actualMomentLockedInnerScaleSource L c
        let Fpa := fun x => Fp x + p.2 * Gp x
        let Fma := fun x => Fm x + p.1 * Gm x
        let Nadj := innerWeightedNorm (7 / 4 : ℝ) Fpa +
          innerWeightedNorm (7 / 4 : ℝ) Fma
        let Fo : ℝ → ℂ := fun x =>
          F0 x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
            (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
        ∀ r ∈ Icc (L / a) B,
          ‖originPhysicalValue K.y r *
              originGreenCoeffA K B Fo r‖ ≤
            G * (1 + (D + 1) * G * (B ^ 2 + 2)) *
                ((actualInnerShellValueConstant +
                  actualInnerShellDerivativeConstant) * Nadj) +
            (G * (1 + (D + 1) * G * B ^ 2) * Q +
              (G ^ 2 * Cs * C) * (N + Q)) := by
  obtain ⟨Ll, el, C, Cs, hLl, hel, helOne, hC, hCs, hLocalSelect⟩ :=
    actual_Hartree_true_source_selected_adjusted_local_Green_no_scale_loss
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨Lt, et, _Ct, hLt, het, hetOne, _hCt, hTransportSelect⟩ :=
    actual_Hartree_true_source_unique_speed_selected_Green_transport
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  let L0 : ℝ := max Ll Lt
  let epsilon : ℝ := min el et
  have hL0 : 6 ≤ L0 := hLl.trans (le_max_left _ _)
  have heps : 0 < epsilon := lt_min hel het
  have hepsOne : epsilon ≤ 1 := (min_le_left _ _).trans helOne
  refine ⟨L0, epsilon, C, Cs, hL0, heps, hepsOne, hC, hCs, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss
  dsimp only
  have hLargeL : Ll ≤ L := (le_max_left _ _).trans hLarge
  have hLargeT : Lt ≤ L := (le_max_right _ _).trans hLarge
  have hSmallL : a * |c| ≤ el := hSmall.trans (min_le_left _ _)
  have hSmallT : a * |c| ≤ et := hSmall.trans (min_le_right _ _)
  obtain ⟨p, hCompat, hUnique, hSize, hLocal⟩ :=
    hLocalSelect L c a hLp hLargeL ha3 hSmallL hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  obtain ⟨q, hCompatT, _hUniqueT, _hSizeT, hTransport⟩ :=
    hTransportSelect L c a hLp hLargeT ha3 hSmallT hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  have hqp : q = p := hUnique q hCompatT
  subst q
  refine ⟨p, hCompat, hUnique, hSize, ?_⟩
  let F0 : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let Q : ℝ :=
    actualHartreePhysicalWeightedSourceConstant Bz Az * ell ^ (1 / 8 : ℝ)
  let N : ℝ :=
    innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp
  let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp
  let Fpa := fun x => Fp x + p.2 * Gp x
  let Fma := fun x => Fm x + p.1 * Gm x
  let hpa := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp p.2
  let hma := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm p.1
  let Nadj := innerWeightedNorm (7 / 4 : ℝ) Fpa +
    innerWeightedNorm (7 / 4 : ℝ) Fma
  let Fo : ℝ → ℂ := fun x =>
    F0 x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
      (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
  let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
  let Cr : ℝ := 1 + (D + 1) * G * (B ^ 2 + 2)
  let Cp : ℝ := 1 + (D + 1) * G * B ^ 2
  let Cf : ℝ := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hLtwo : 2 < L := by linarith [hLarge, hL0]
  have hr0 : 0 < L / a := div_pos hLp ha
  have hSpeedCont := actual_Hartree_moment_locked_inner_sources_continuous L c
  have hcpa : Continuous Fpa := by
    dsimp [Fpa, Gp]
    exact hcp.add (continuous_const.mul hSpeedCont.2)
  have hcma : Continuous Fma := by
    dsimp [Fma, Gm]
    exact hcm.add (continuous_const.mul hSpeedCont.1)
  have hTraceRaw :=
    actual_Hartree_original_Fredholm_outgoing_trace_source_radius_gain
      K D G B L a hD hG hB hBOne hBR.le hcoeff hbound
      hLtwo ha hOrder Fpa Fma hpa hma hcpa hcma
  have hTrace :
      ‖actualOriginOutgoingTrace K (L / a) J.1 J.2‖ ≤
        Cr * (L / a) * (Cf * Nadj) := by
    simpa only [J, Cr, Cf, Nadj] using hTraceRaw
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hCf : 0 ≤ Cf := by
    dsimp [Cf, actualInnerShellValueConstant, actualInnerShellDerivativeConstant]
    positivity
  have hNadj : 0 ≤ Nadj := by
    dsimp [Nadj]
    exact add_nonneg
      (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hCoef : 0 ≤ G * Cr * (Cf * Nadj) := by positivity
  intro r hr
  have hrpos : 0 < r := hr0.trans_le hr.1
  have hY : ‖originPhysicalValue K.y r‖ ≤ G / r := by
    have hBr := hbound r ⟨hrpos.le, hr.2.trans hBR.le⟩
    rw [originPhysicalValue, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrpos]
    exact div_le_div_of_nonneg_right hBr.1 hrpos.le
  have hRatio : (L / a) / r ≤ 1 :=
    (div_le_iff₀ hrpos).2 (by linarith [hr.1])
  have hTraceProduct :
      ‖originPhysicalValue K.y r *
        actualOriginOutgoingTrace K (L / a) J.1 J.2‖ ≤
        G * Cr * (Cf * Nadj) := by
    calc
      _ = ‖originPhysicalValue K.y r‖ *
        ‖actualOriginOutgoingTrace K (L / a) J.1 J.2‖ := norm_mul _ _
      _ ≤ (G / r) * (Cr * (L / a) * (Cf * Nadj)) :=
        mul_le_mul hY hTrace (norm_nonneg _) (div_nonneg hG hrpos.le)
      _ = (G * Cr * (Cf * Nadj)) * ((L / a) / r) := by
        field_simp [hrpos.ne']
      _ ≤ (G * Cr * (Cf * Nadj)) * 1 :=
        mul_le_mul_of_nonneg_left hRatio hCoef
      _ = G * Cr * (Cf * Nadj) := by ring
  have hLocalBound :
      ‖originPhysicalValue K.y r *
          originGreenCoeffA K r Fo (L / a)‖ ≤
        G * Cp * Q + (G ^ 2 * Cs * C) * (N + Q) := by
    simpa only [Fo, Cp] using hLocal r hr
  have hTransportEq :
      originGreenCoeffA K B Fo r =
        actualOriginOutgoingTrace K (L / a) J.1 J.2 -
          originGreenCoeffA K r Fo (L / a) := by
    simpa only [Fo, J, originGreenCoeffA] using hTransport r hr
  calc
    ‖originPhysicalValue K.y r * originGreenCoeffA K B Fo r‖ =
      ‖originPhysicalValue K.y r *
          actualOriginOutgoingTrace K (L / a) J.1 J.2 -
        originPhysicalValue K.y r *
          originGreenCoeffA K r Fo (L / a)‖ := by
          rw [hTransportEq, mul_sub]
    _ ≤ ‖originPhysicalValue K.y r *
          actualOriginOutgoingTrace K (L / a) J.1 J.2‖ +
        ‖originPhysicalValue K.y r *
          originGreenCoeffA K r Fo (L / a)‖ := norm_sub_le _ _
    _ ≤ G * Cr * (Cf * Nadj) +
        (G * Cp * Q + (G ^ 2 * Cs * C) * (N + Q)) :=
      add_le_add hTraceProduct hLocalBound

end HBL.TypeIIDynamicSelection
