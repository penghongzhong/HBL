import HBL.TypeIIDynamicSelection.ActualHartreeGeneralSourceCorrection
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedBackwardShell
import HBL.TypeIIDynamicSelection.ActualHartreeBackwardShellRegion

/-!
# A relative matched-shell estimate for arbitrary coherent sources

The base input need not be a core/radiation interaction. Its two real
inner sources and full outer RHS must be the same physical forcing on
[L/2,L]. This is an exact source identity, not a residual gain hypothesis.
The actual velocity correction preserves that identity. The same fixed
inverse and same matched Kummer field then produce a relative shell bound
C (L/2)^(-3/4) (N0+Q), for every source in the specified class.

Q is the raw outer source envelope: |F(r)| <= Q/r^2 on [L/a,B].
The conclusion does not estimate time dependence, the global Hartree
feedback, or radiation at infinity and does not close manuscript 2.13.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.Profile.Kummer

/-- The natural radial partition of ANY complex physical source has the
exact inner/outer coherence used below; no Hartree source formula is needed. -/
theorem actual_Hartree_general_radial_partition_coherent
    (L a y : ℝ) (S : ℝ → ℂ) (hL : 0 < L) (ha : 0 < a)
    (hy : 0 < y) (hyL : y ≤ L) :
    let Fp := fun r => ((((r * actualHartreeInnerSourceCutoff L r : ℝ) : ℂ) * S r).re)
    let Fm := fun r => ((((r * actualHartreeInnerSourceCutoff L r : ℝ) : ℂ) * S r).im)
    let F := fun r => -((a ^ 2 : ℝ) : ℂ) * S (a * r)
    ((a ^ 2)⁻¹ : ℝ) • F (y / a) + actualHartreeTwoChannelPhysicalSource Fp Fm y = 0 := by
  dsimp only
  have hCut := actual_Hartree_inner_source_cutoff_one L y hL hyL
  have hPair (v : ℂ) : (v.re : ℂ) + Complex.I * (v.im : ℂ) = v := by
    apply Complex.ext <;> simp
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hPhysical : actualHartreeTwoChannelPhysicalSource
      (fun r => ((((r * actualHartreeInnerSourceCutoff L r : ℝ) : ℂ) * S r).re))
      (fun r => ((((r * actualHartreeInnerSourceCutoff L r : ℝ) : ℂ) * S r).im)) y = S y := by
    unfold actualHartreeTwoChannelPhysicalSource
    rw [hPair, hCut, mul_one]
    field_simp [hyC]
  have hScale : a * (y / a) = y := by field_simp [ha.ne']
  have hUnit : (((a ^ 2)⁻¹ : ℝ) : ℂ) * ((a ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne'), Complex.ofReal_one]
  rw [hPhysical, hScale]
  simp only [Complex.real_smul]
  linear_combination -(S y) * hUnit

private theorem general_plateau_velocity_coherence
    (L c a y db dw : ℝ) (Fp Fm : ℝ → ℝ) (F : ℝ → ℂ)
    (hL : 0 < L) (ha : 0 < a) (hy : 0 < y) (hyL : y ≤ L)
    (hBase : ((a ^ 2)⁻¹ : ℝ) • F (y / a) +
      actualHartreeTwoChannelPhysicalSource Fp Fm y = 0) :
    let Fpa := fun r => Fp r + dw * actualMomentLockedInnerPhaseSource L c r
    let Fma := fun r => Fm r + db * actualMomentLockedInnerScaleSource L c r
    let Fo := fun r => F r - (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
      (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
    ((a ^ 2)⁻¹ : ℝ) • Fo (y / a) + actualHartreeTwoChannelPhysicalSource Fpa Fma y = 0 := by
  dsimp only
  have hSpeed := actual_Hartree_moment_locked_inner_sources_core L c y hL ⟨hy, hyL⟩
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hNumerator : (Fp y : ℂ) + Complex.I * (Fm y : ℂ) =
      (y : ℂ) * actualHartreeTwoChannelPhysicalSource Fp Fm y := by
    unfold actualHartreeTwoChannelPhysicalSource
    field_simp [hyC]
  have hSource : actualHartreeTwoChannelPhysicalSource
      (fun r => Fp r + dw * actualMomentLockedInnerPhaseSource L c r)
      (fun r => Fm r + db * actualMomentLockedInnerScaleSource L c r) y =
      actualHartreeTwoChannelPhysicalSource Fp Fm y +
        (db : ℂ) * actualMomentLockedScaleSource c y +
        (dw : ℂ) * actualMomentLockedPhaseSource c y := by
    unfold actualHartreeTwoChannelPhysicalSource
    apply (div_eq_iff hyC).2
    push_cast
    linear_combination hNumerator + (db : ℂ) * hSpeed.1 + (dw : ℂ) * hSpeed.2
  rw [hSource]
  have hScale : a * (y / a) = y := by field_simp [ha.ne']
  have hUnit : (((a ^ 2)⁻¹ : ℝ) : ℂ) * ((a ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne'), Complex.ofReal_one]
  unfold actualMomentLockedScaledScaleSource actualMomentLockedScaledPhaseSource
  rw [hScale]
  simp only [Complex.real_smul] at hBase ⊢
  linear_combination hBase - ((db : ℂ) * actualMomentLockedScaleSource c y +
    (dw : ℂ) * actualMomentLockedPhaseSource c y) * hUnit

/-- Genuine source-relative shell gain for arbitrary coherent inputs.
No inner solution, exterior solution, matching jet, speed correction,
compatibility smallness or shell estimate is supplied as a hypothesis.
All displayed fields use the same normalized inverse and full outer RHS. -/
theorem actual_Hartree_general_source_matched_shell_region
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C : ℝ, 6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < C ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
      ∀ (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
        Continuous Fp → Continuous Fm →
      ∀ (F : ℝ → ℂ) (Q : ℝ), 0 ≤ Q →
        IntervalIntegrable F volume (L / a) B →
        (∀ r ∈ Icc (L / a) B, ‖F r‖ ≤ Q / r ^ 2) →
        (∀ y ∈ Icc (L / 2) L, ((a ^ 2)⁻¹ : ℝ) • F (y / a) +
          actualHartreeTwoChannelPhysicalSource Fp Fm y = 0) →
        (∀ db dw r : ℝ, r ∈ Ioo 0 scale → ContinuousAt (fun t =>
          F t - (db : ℂ) * actualMomentLockedScaledScaleSource a c t -
            (dw : ℂ) * actualMomentLockedScaledPhaseSource a c t) r) →
        let N0 := innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm
        ∃ p : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F p.1 p.2 = 0 ∧
          (∀ q : ℝ × ℝ,
            actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
              Fp Fm hp hm F q.1 q.2 = 0 → q = p) ∧
          let Fpa := fun r => Fp r + p.2 * actualMomentLockedInnerPhaseSource L c r
          let Fma := fun r => Fm r + p.1 * actualMomentLockedInnerScaleSource L c r
          let Fo := fun r => F r - (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c r -
            (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c r
          ∃ (hpa : InWeightedL2 (7 / 4 : ℝ) Fpa) (hma : InWeightedL2 (7 / 4 : ℝ) Fma),
          let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
          let w := actualOriginMatchedKummerValue K (L / a) B Fo J.1 J.2
          let v := actualOriginMatchedKummerPullback K a (L / a) B Fo J.1 J.2
          let d := fun r => actualHartreeTwoChannelInner Fpa Fma hpa hma r - v r
          let E := actualMatchedKummerShellError mu theta a (L / 2) d
          InWeightedL2 (7 / 4 : ℝ) (actualConjugatedShellMagnitude (L / 2) E) ∧
          innerWeightedNorm (7 / 4 : ℝ) (actualConjugatedShellMagnitude (L / 2) E) ≤
            C * (L / 2) ^ (-(3 / 4 : ℝ)) * (N0 + Q) ∧
          actualOriginOutgoingTrace K B (w B) (deriv w B) = 0 := by
  obtain ⟨Lc, epsilon, Cc, hLc, hepsilon, hepsOne, hCc, hCorrection⟩ :=
    actual_Hartree_general_source_correction_region K D G B hD hG hB hBR hcoeff hbound hsmallB
  obtain ⟨Cs, hCs, hWeighted⟩ := actual_Hartree_two_channel_matched_shell_weighted_gain
  let L0 := max Lc (max 6 (4 * (1 + ‖frozenZeroCoeff mu theta‖)))
  let H := 1 + |actualInnerShellEquationConstant| + |actualInnerShellKummerConstant mu theta|
  have hH : 0 < H := by dsimp [H]; positivity
  have hL0 : 6 ≤ L0 := hLc.trans (le_max_left _ _)
  refine ⟨L0, epsilon, 20 * Cs * H * (1 + Cc), hL0, hepsilon, hepsOne, by positivity, ?_⟩
  intro L c a hLp hLarge ha3 hSmall Fp Fm hp hm hcp hcm F Q hQ hF hEnvelope hSame hOuter
  dsimp only
  have hLargeC : Lc ≤ L := (le_max_left _ _).trans hLarge
  have hExtra : max 6 (4 * (1 + ‖frozenZeroCoeff mu theta‖)) ≤ L :=
    (le_max_right _ _).trans hLarge
  have hLsix : 6 ≤ L := (le_max_left _ _).trans hExtra
  have hLone : 1 ≤ L := by linarith
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  obtain ⟨_hc, _hLcSmall, hr0, hLB, p, hCompat, hUnique, hAdjusted⟩ :=
    hCorrection L c a hLp hLargeC ha3 hSmall Fp Fm hp hm hcp hcm F Q hQ hF hEnvelope
  let R := L / 2
  let Fpa := fun r => Fp r + p.2 * actualMomentLockedInnerPhaseSource L c r
  let Fma := fun r => Fm r + p.1 * actualMomentLockedInnerScaleSource L c r
  let Fo := fun r => F r - (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c r -
    (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c r
  have hpa : InWeightedL2 (7 / 4 : ℝ) Fpa := innerWeighted_add_smul_mem
    (7 / 4 : ℝ) Fp _ hp (actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp) p.2
  have hma : InWeightedL2 (7 / 4 : ℝ) Fma := innerWeighted_add_smul_mem
    (7 / 4 : ℝ) Fm _ hm (actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp) p.1
  have hCont := actual_Hartree_moment_locked_inner_sources_continuous L c
  have hcpa : Continuous Fpa := hcp.add (continuous_const.mul hCont.2)
  have hcma : Continuous Fma := hcm.add (continuous_const.mul hCont.1)
  have hFo : ∀ r ∈ Ioo 0 scale, ContinuousAt Fo r := hOuter p.1 p.2
  let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
  let w := actualOriginMatchedKummerValue K (L / a) B Fo J.1 J.2
  let v := actualOriginMatchedKummerPullback K a (L / a) B Fo J.1 J.2
  let d := fun r => actualHartreeTwoChannelInner Fpa Fma hpa hma r - v r
  let E := actualMatchedKummerShellError mu theta a R d
  let U : Set ℝ := Ioo 0 (a * scale)
  have hWeak := actual_Hartree_backward_shell_weak_budget mu theta L a hExtra ha3
  have hR : 2 < R := hWeak.1
  have hRpos : 0 < R := by linarith
  have hTwoR : 2 * R = L := by dsimp [R]; ring
  have hLupper : L < a * scale := by
    have h := (div_lt_iff₀ ha).1 (hLB.trans_lt hBR)
    simpa only [mul_comm] using h
  have hSub : Icc R (2 * R) ⊆ U := by
    intro x hx
    exact ⟨hRpos.trans_le hx.1, (hx.2.trans_eq hTwoR).trans_lt hLupper⟩
  have hAnchor : L ∈ Icc R (2 * R) := by
    refine ⟨?_, ?_⟩
    · dsimp [R]; linarith
    · rw [hTwoR]
  have hClass := actual_Hartree_matched_Kummer_pullback_classical K a ha
    hr0 hLB hBR Fo hFo J.1 J.2
  have hv : ∀ x ∈ U, DifferentiableAt ℝ v x := fun x hx => (hClass x hx).1.differentiableAt
  have hv2 : ∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv v) x :=
    fun x hx => (hClass x (hSub hx)).2.1
  have hJet := actual_Hartree_moment_locked_pullback_actual_inner_jet
    K L a hLp ha hLB hBR Fpa Fma hpa hma Fo hFo
  have hleft : actualHartreeTwoChannelInner Fpa Fma hpa hma L = v L := hJet.1.symm
  have hdleft : deriv (actualHartreeTwoChannelInner Fpa Fma hpa hma) L = deriv v L := hJet.2.2.1.symm
  have hEquation : ∀ x ∈ Icc R (2 * R),
      actualMatchedScaledKummerApply mu theta a v x = -actualHartreeTwoChannelPhysicalSource Fpa Fma x := by
    intro x hx
    rw [(hClass x (hSub hx)).2.2]
    have hxL : x ≤ L := hx.2.trans_eq hTwoR
    exact eq_neg_of_add_eq_zero_left (general_plateau_velocity_coherence
      L c a x p.1 p.2 Fp Fm F hLp ha (hSub hx).1 hxL (hSame x ⟨hx.1, hxL⟩))
  have hw := hWeighted mu theta a R L Fpa Fma hpa hma U v
    hcpa hcma isOpen_Ioo hSub ha hR hWeak.2 hAnchor hv hv2 hleft hdleft hEquation
  let N0 := innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm
  let Na := innerWeightedNorm (7 / 4 : ℝ) Fpa + innerWeightedNorm (7 / 4 : ℝ) Fma
  have hN0 : 0 ≤ N0 := add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hNa : 0 ≤ Na := add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hPow : L ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hLone
      (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
  have hNaBound : Na ≤ (1 + Cc) * (N0 + Q) := by
    calc
      _ ≤ N0 + Cc * L ^ (-(1 / 2 : ℝ)) * (N0 + Q) := hAdjusted
      _ ≤ N0 + Cc * (N0 + Q) := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPow hCc.le)
          (add_nonneg hN0 hQ)
        simpa only [mul_one] using _root_.add_le_add (le_refl N0) h
      _ ≤ (1 + Cc) * (N0 + Q) := by nlinarith only [hQ]
  have hKnonneg : 0 ≤ actualInnerShellKummerConstant mu theta := by
    dsimp [actualInnerShellKummerConstant, actualInnerShellDerivativeConstant,
      actualInnerShellValueConstant]
    positivity
  have hFactor := actual_Hartree_backward_shell_relative_factor L a
    actualInnerShellEquationConstant (actualInnerShellKummerConstant mu theta)
    (by linarith) ha3 hKnonneg
  have hCoeff : actualInnerShellEquationConstant + actualInnerShellKummerConstant mu theta ≤ H := by
    dsimp [H]
    linarith [le_abs_self actualInnerShellEquationConstant, le_abs_self (actualInnerShellKummerConstant mu theta)]
  refine ⟨p, hCompat, hUnique, hpa, hma, hw.1, ?_, ?_⟩
  · calc
      _ ≤ 20 * Cs * (actualInnerShellEquationConstant * R ^ (-(3 / 4 : ℝ)) +
          actualInnerShellKummerConstant mu theta * R ^ (13 / 4 : ℝ) / a ^ 2) * Na := hw.2.2
      _ ≤ 20 * Cs * ((actualInnerShellEquationConstant + actualInnerShellKummerConstant mu theta) *
          R ^ (-(3 / 4 : ℝ))) * Na :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFactor (by positivity)) hNa
      _ ≤ 20 * Cs * (H * R ^ (-(3 / 4 : ℝ))) * Na :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hCoeff (Real.rpow_nonneg hRpos.le _)) (by positivity)) hNa
      _ ≤ 20 * Cs * (H * R ^ (-(3 / 4 : ℝ))) * ((1 + Cc) * (N0 + Q)) :=
        mul_le_mul_of_nonneg_left hNaBound (by positivity)
      _ = _ := by ring
  · exact (actual_origin_matched_Kummer_actual_upper_trace K hr0 hLB hBR Fo hFo J.1 J.2).trans hCompat

end HBL.TypeIIDynamicSelection
