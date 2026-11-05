import HBL.TypeIIDynamicSelection.ActualHartreeMatchedExteriorEnvelope

/-!
# Original-input bounds after the SAME compatible speed correction

Reuse the general-source correction, its complete inverse bound, the actual
speed envelope, and the actual matched-annulus feedback. The output does
not take a bound for adjusted sources or an inverse estimate as a premise.
All source norms, traces, real speeds and fields refer to one construction.
This controls the finite annulus only, not the full PDE residual or infinity.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

/-- The unique selected real pair has both its adjusted inner norm and its
FULL adjusted exterior envelope controlled by the original input size.
The constant and physical thresholds precede the source functions. -/
theorem actual_Hartree_selected_corrected_source_bounds_region
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B)
    (hBOne : B ≤ 1) (hBR : B < scale)
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
        ∃ (p : ℝ × ℝ) (Qa : ℝ),
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F p.1 p.2 = 0 ∧
          (∀ q : ℝ × ℝ,
            actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
              Fp Fm hp hm F q.1 q.2 = 0 → q = p) ∧
          0 ≤ Qa ∧ L / a ≤ B ∧
          (∀ r ∈ Icc (L / a) B,
            ‖F r - (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c r -
                (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c r‖ ≤ Qa / r ^ 2) ∧
          innerWeightedNorm (7 / 4 : ℝ)
              (fun r => Fp r + p.2 * actualMomentLockedInnerPhaseSource L c r) +
            innerWeightedNorm (7 / 4 : ℝ)
              (fun r => Fm r + p.1 * actualMomentLockedInnerScaleSource L c r) + Qa ≤
            C * (innerWeightedNorm (7 / 4 : ℝ) Fp +
              innerWeightedNorm (7 / 4 : ℝ) Fm + Q) := by
  obtain ⟨Lc, ec, Cc, hLc, hec, hecOne, hCc, hCorrection⟩ :=
    actual_Hartree_general_source_correction_region K D G B hD hG hB hBR
      hcoeff hbound hsmallB
  obtain ⟨Li, ei, _hLi, hei, hInverse⟩ :=
    actual_Hartree_moment_locked_coupled_inverse_bound_region K D G hD hG hB hBR
      hcoeff hbound hsmallB
  obtain ⟨M, hM, hEnvelope⟩ := actual_Hartree_corrected_outer_envelope
  let CT := actualMomentLockedObstructionTraceConstant D G B
  let CK := 1 + (D + 1) * G * B ^ 2
  let ZC := CT + CK * B
  let A := 1024 * M * ZC / B
  have hCT : 0 ≤ CT := by
    dsimp [CT, actualMomentLockedObstructionTraceConstant,
      actualInnerShellValueConstant, actualInnerShellDerivativeConstant]
    positivity
  have hCK : 0 ≤ CK := by dsimp [CK]; positivity
  have hZC : 0 ≤ ZC := by dsimp [ZC]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let L0 := max Lc Li
  let epsilon := min ec ei
  have hL0 : 6 ≤ L0 := hLc.trans (le_max_left _ _)
  have hepsOne : epsilon ≤ 1 := (min_le_left _ _).trans hecOne
  refine ⟨L0, epsilon, 2 + Cc + A, hL0, lt_min hec hei, hepsOne, by positivity, ?_⟩
  intro L c a hLp hLarge ha3 hSmall Fp Fm hp hm hcp hcm F Q hQ hF hFBound
  have hLargeC : Lc ≤ L := (le_max_left _ _).trans hLarge
  have hLargeI : Li ≤ L := (le_max_right _ _).trans hLarge
  have hSmallC : a * |c| ≤ ec := hSmall.trans (min_le_left _ _)
  have hSmallI : a * |c| ≤ ei := hSmall.trans (min_le_right _ _)
  have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
  have hLsix : 6 ≤ L := hL0.trans hLarge
  have hLone : 1 ≤ L := by linarith
  have hLtwo : 2 < L := by linarith
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have haOne : 1 ≤ a := (one_le_pow₀ hLone).trans ha3
  obtain ⟨hc, _hLc, hr0, hLB, p, hCompat, hUnique, hAdjusted⟩ :=
    hCorrection L c a hLp hLargeC ha3 hSmallC Fp Fm hp hm hcp hcm F Q hQ hF hFBound
  let N0 := innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm
  let E := N0 + Q
  have hN0 : 0 ≤ N0 := add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hE : 0 ≤ E := add_nonneg hN0 hQ
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let Z := actualMomentLockedIntervalObstruction K (L / a) B F J.1 J.2
  have hTrace := actual_Hartree_canonical_baseline_outgoing_trace_bound
    K D G B L a hD hG hBR hLtwo ha3 hLB hcoeff hbound Fp Fm hp hm hcp hcm
  have hGreen := (actual_general_source_Green_coefficient_bound
    K D G B (L / a) Q hD hG hQ hr0 hLB hBR hcoeff hbound F hF hFBound).2
  have hZ : ‖Z‖ ≤ CT / a * N0 + CK * B * Q :=
    (norm_sub_le _ _).trans (add_le_add hTrace hGreen)
  have hT : CT / a * N0 ≤ CT * E :=
    (mul_le_mul_of_nonneg_right (div_le_self hCT haOne) hN0).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hQ) hCT)
  have hGQ : CK * B * Q ≤ CK * B * E :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hN0) (mul_nonneg hCK hB.le)
  have hZtotal : ‖Z‖ ≤ ZC * E :=
    (hZ.trans (add_le_add hT hGQ)).trans_eq (by dsimp [ZC]; ring)
  have hSpeed := hInverse L c a hLp hLargeI ha3 hc hSmallI Fp Fm hp hm F hF
    p.1 p.2 hCompat
  have hSpeedOriginal : |p.1| + |p.2| ≤ 1024 / (a * B ^ 2) * (ZC * E) :=
    hSpeed.trans (mul_le_mul_of_nonneg_left hZtotal (by positivity))
  let Qa := Q + M * a * B * (|p.1| + |p.2|)
  have hQa : 0 ≤ Qa := by dsimp [Qa]; positivity
  have hQaBound : Qa ≤ (1 + A) * E := by
    calc
      _ ≤ Q + M * a * B * (1024 / (a * B ^ 2) * (ZC * E)) :=
        _root_.add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hSpeedOriginal (by positivity : 0 ≤ M * a * B))
      _ = Q + A * E := by dsimp [A]; field_simp [ha.ne', hB.ne']
      _ ≤ (1 + A) * E := by dsimp [E]; nlinarith only [hN0]
  have hPow : L ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hLone (by norm_num)
  have hNAdjusted : innerWeightedNorm (7 / 4 : ℝ)
        (fun r => Fp r + p.2 * actualMomentLockedInnerPhaseSource L c r) +
      innerWeightedNorm (7 / 4 : ℝ)
        (fun r => Fm r + p.1 * actualMomentLockedInnerScaleSource L c r) ≤ (1 + Cc) * E := by
    calc
      _ ≤ N0 + Cc * L ^ (-(1 / 2 : ℝ)) * E := hAdjusted
      _ ≤ N0 + Cc * E := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPow hCc.le) hE
        nlinarith only [h]
      _ ≤ (1 + Cc) * E := by dsimp [E]; nlinarith only [hQ]
  refine ⟨p, Qa, hCompat, hUnique, hQa, hLB, ?_, ?_⟩
  · exact hEnvelope L c a B hLone ha hBOne hSmallOne F Q p.1 p.2 hFBound
  · exact (add_le_add hNAdjusted hQaBound).trans_eq (by ring)

/-- After the actual unique compatibility solve, the matched-annulus
Hartree feedback is relative to the ORIGINAL source pair and outer envelope.
Regularity of the corrected RHS is derived. No adjusted-size estimate,
selected speed, matched field, or inverse bound is an input. -/
theorem actual_Hartree_selected_exterior_feedback_region
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B)
    (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧ ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C : ℝ, 6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < C ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
      ∀ (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm), Continuous Fp → Continuous Fm →
      ∀ (F : ℝ → ℂ) (Q : ℝ), 0 ≤ Q →
        IntervalIntegrable F volume (L / a) B →
        (∀ x ∈ Ioo 0 scale, ContinuousAt F x) →
        (∀ x ∈ Icc (L / a) B, ‖F x‖ ≤ Q / x ^ 2) →
        ∃ p : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F p.1 p.2 = 0 ∧
          (∀ q : ℝ × ℝ,
            actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
              Fp Fm hp hm F q.1 q.2 = 0 → q = p) ∧
          let Fpa := fun y => Fp y + p.2 * actualMomentLockedInnerPhaseSource L c y
          let Fma := fun y => Fm y + p.1 * actualMomentLockedInnerScaleSource L c y
          let Fo := fun x => F x - (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c x -
            (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c x
          ∃ (hpa : InWeightedL2 (7 / 4 : ℝ) Fpa) (hma : InWeightedL2 (7 / 4 : ℝ) Fma),
          let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
          let qext := fun y => y *
            (actualOriginMatchedKummerValue K (L / a) B Fo J.1 J.2 (y / a)).re
          ∀ r : ℝ, 0 < r → 2 * r ≤ L →
            IntervalIntegrable (fun y => hartreeKernel r y * qext y) volume L (a * B) ∧
            |∫ y in L..(a * B), hartreeKernel r y * qext y| ≤
              C * (innerWeightedNorm (7 / 4 : ℝ) Fp +
                innerWeightedNorm (7 / 4 : ℝ) Fm + Q) * r * bubble r ^ 3 / L ^ 2 := by
  obtain ⟨L0, epsilon, C0, hL0, hepsilon, hepsOne, hC0, hBounds⟩ :=
    actual_Hartree_selected_corrected_source_bounds_region K D G B hD hG hB hBOne hBR
      hcoeff hbound hsmallB
  let A := 32 * Real.pi * hartreeKappa * actualMatchedExteriorSourceConstant D G B
  have hA : 0 ≤ A := by
    dsimp [A, actualMatchedExteriorSourceConstant, actualMatchedExteriorGrowthConstant,
      actualInnerShellValueConstant, actualInnerShellDerivativeConstant, hartreeKappa]
    positivity
  refine ⟨L0, epsilon, 1 + A * C0, hL0, hepsilon, hepsOne, by positivity, ?_⟩
  intro L c a hLp hLarge ha3 hSmall Fp Fm hp hm hcp hcm F Q hQ hF hFC hEnvelope
  have hL : 2 < L := by linarith [hL0.trans hLarge]
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  obtain ⟨p, Qa, hCompat, hUnique, hQa, hLB, hEnv, hSize⟩ :=
    hBounds L c a hLp hLarge ha3 hSmall Fp Fm hp hm hcp hcm F Q hQ hF hEnvelope
  refine ⟨p, hCompat, hUnique, ?_⟩
  dsimp only
  let Fpa := fun y => Fp y + p.2 * actualMomentLockedInnerPhaseSource L c y
  let Fma := fun y => Fm y + p.1 * actualMomentLockedInnerScaleSource L c y
  let Fo := fun x => F x - (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c x -
    (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c x
  have hpa : InWeightedL2 (7 / 4 : ℝ) Fpa :=
    innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp _ hp
      (actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp) p.2
  have hma : InWeightedL2 (7 / 4 : ℝ) Fma :=
    innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm _ hm
      (actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp) p.1
  have hSpeedCont := actual_Hartree_moment_locked_inner_sources_continuous L c
  have hcpa : Continuous Fpa := hcp.add (continuous_const.mul hSpeedCont.2)
  have hcma : Continuous Fma := hcm.add (continuous_const.mul hSpeedCont.1)
  have hFo : ∀ x ∈ Ioo 0 scale, ContinuousAt Fo x := fun x hx =>
    actual_Hartree_corrected_outer_source_continuousAt a c p.1 p.2 x ha hx.1 F (hFC x hx)
  refine ⟨hpa, hma, ?_⟩
  intro r hr hsep
  have hTail := actual_Hartree_matched_exterior_core_feedback K D G B L a hD hG
    hL ha hLB hBOne hBR hcoeff hbound Fpa Fma hpa hma hcpa hcma Fo Qa hQa hFo hEnv r hr hsep
  refine ⟨hTail.1, hTail.2.trans ?_⟩
  let E := innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm + Q
  have hE : 0 ≤ E := add_nonneg
    (add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)) hQ
  have hBudget := mul_le_mul_of_nonneg_left hSize hA
  have hGeom : 0 ≤ r * bubble r ^ 3 / L ^ 2 := by
    have hb := bubble_nonneg r
    positivity
  have hFinal := mul_le_mul_of_nonneg_right
    (hBudget.trans (show A * (C0 * E) ≤ (1 + A * C0) * E by nlinarith only [hE])) hGeom
  convert hFinal using 1 <;> dsimp [A] <;> ring

end HBL.TypeIIDynamicSelection
