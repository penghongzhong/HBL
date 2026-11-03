import HBL.InnerReconstruction.UniformMomentOperatorBound
import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedInnerChargeGain
import HBL.TypeIIDynamicSelection.ActualHartreeEighthEnvelopeL2Integral
import Mathlib.Tactic

/-!
Same physical Hartree source -> uniformly small canonical inner moments.
All constants are chosen BEFORE ell,c,z. The actual fixed Fredholm inverse,
corrected weighted source, and forced affine charges are reused. Neither
moment smallness nor a trace bound is a hypothesis. The source is the
correct conjugated r*(1-chi)*F; this does not yet treat the complete
iterated residual, simultaneous Kummer/remote matching or the Type-II law.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

private theorem criticalTail_memLp :
    MemLp (fun r : ℝ => (1 + r) ^ (-(5 / 8 : ℝ))) 2 halfLineMeasure := by
  have hm : Measurable (fun r : ℝ => (1 + r) ^ (-(5 / 8 : ℝ))) := by fun_prop
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable.restrict).2
    actual_Hartree_eighth_weighted_envelope_square_integrable

private def criticalTailL2 : RealL2 halfLineMeasure :=
  criticalTail_memLp.toLp (fun r : ℝ => (1 + r) ^ (-(5 / 8 : ℝ)))

private theorem sourceData_norm_of_envelope
    (F : ℝ → ℝ) (hF : InWeightedL2 (7 / 4 : ℝ) F) (C : ℝ)
    (hBound : ∀ r : ℝ, 0 < r →
      affineJapaneseWeight (7 / 4 : ℝ) r * |F r| ≤
        C * (1 + r) ^ (-(5 / 8 : ℝ))) :
    ‖weightedSourceDataL2 (7 / 4 : ℝ) F hF‖ ≤ C * ‖criticalTailL2‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedSourceDataL2_ae (7 / 4 : ℝ) F hF,
    criticalTail_memLp.coeFn_toLp,
    ae_restrict_mem measurableSet_Ioi] with r hd ht hr
  have hr0 : 0 < r := hr
  have hw : 0 ≤ affineJapaneseWeight (7 / 4 : ℝ) r := by
    unfold affineJapaneseWeight
    positivity
  have ht0 : 0 ≤ (1 + r) ^ (-(5 / 8 : ℝ)) := by positivity
  change ‖weightedSourceDataL2 (7 / 4 : ℝ) F hF r‖ ≤ C * ‖criticalTailL2 r‖
  rw [hd, ht, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hw, abs_of_nonneg ht0]
  exact hBound r hr0

private theorem correctedData_norm_le
    (F P : ℝ → ℝ) (a : ℝ)
    (hF : InWeightedL2 (7 / 4 : ℝ) F)
    (hP : InWeightedL2 (7 / 4 : ℝ) P)
    (hC : InWeightedL2 (7 / 4 : ℝ) (fun r => F r - a * P r)) :
    ‖weightedSourceDataL2 (7 / 4 : ℝ) (fun r => F r - a * P r) hC‖ ≤
      ‖weightedSourceDataL2 (7 / 4 : ℝ) F hF‖ +
        |a| * ‖weightedSourceDataL2 (7 / 4 : ℝ) P hP‖ := by
  let f := weightedSourceDataL2 (7 / 4 : ℝ) F hF
  let p := weightedSourceDataL2 (7 / 4 : ℝ) P hP
  have heq : weightedSourceDataL2 (7 / 4 : ℝ)
      (fun r => F r - a * P r) hC = f - a • p := by
    apply Lp.ext
    filter_upwards [
      weightedSourceDataL2_ae (7 / 4 : ℝ) (fun r => F r - a * P r) hC,
      weightedSourceDataL2_ae (7 / 4 : ℝ) F hF,
      weightedSourceDataL2_ae (7 / 4 : ℝ) P hP,
      Lp.coeFn_sub f (a • p), Lp.coeFn_smul a p] with r hc hf hp hsub hsmul
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsub hsmul
    rw [hc, hsub, hsmul, hf, hp]
    ring
  rw [heq]
  exact (norm_sub_le f (a • p)).trans_eq (by rw [norm_smul, Real.norm_eq_abs])

/-- Uniform physical-length moment bounds and quantitative traces of the
actual normalized inner correction. Cp,Cm depend on B,A and the fixed
operators only: they precede ell,c,z in the quantifiers. The equations
and canonical Green definitions are retained in the exported conclusion. -/
theorem actual_Hartree_uniform_canonical_inner_moments_and_traces
    (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ Cp Cm : ℝ, 0 ≤ Cp ∧ 0 ≤ Cm ∧
    ∀ (ell c : ℝ) (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
      (z : ℝ → ℂ) (hz : Measurable z)
      (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
      (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A),
    let G := actualHartreeRadiallyConjugatedInnerSource
      (actualHartreeSlowInnerRadius ell) ell c z
    let gp : ℝ → ℝ := fun r => (G r).re
    let gm : ℝ → ℝ := fun r => (G r).im
    ∃ (hp : InWeightedL2 (7 / 4 : ℝ) gp)
      (hm : InWeightedL2 (7 / 4 : ℝ) gm),
    ∃ x : InnerCorrections,
      (1 - weightedBirmanSchwingerOperator) (x.1 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
          (weightedSourceDataL2 (7 / 4 : ℝ) (correctedPlusSource gp)
            (correctedPlusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) gp hp)) ∧
      (1 - weightedPhaseBirman) (x.2 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
          (weightedSourceDataL2 (7 / 4 : ℝ) (correctedMinusSource gm)
            (correctedMinusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) gm hm)) ∧
      innerGreenBound (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
          (correctedPlusSource gp) ≤ Cp * ell ^ (1 / 16 : ℝ) ∧
      innerGreenBound ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
          (correctedMinusSource gm) ≤ Cm * ell ^ (1 / 16 : ℝ) ∧
      (let qp := affineRestore
          (innerGreenRepresentative (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
            (correctedPlusSource gp)) (actualPlusCharge gp)
       let qm := affineRestore
          (innerGreenRepresentative ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
            (correctedMinusSource gm)) (actualMinusCharge gm)
       ∀ r : ℝ, 2 < r →
         |qp r / r - actualPlusCharge gp| ≤ Cp * ell ^ (1 / 16 : ℝ) / r ∧
         |deriv (fun t : ℝ => qp t / t) r| ≤ Cp * ell ^ (1 / 16 : ℝ) / r ^ 2 ∧
         |qm r / r - actualMinusCharge gm| ≤ Cm * ell ^ (1 / 16 : ℝ) / r ∧
         |deriv (fun t : ℝ => qm t / t) r| ≤ Cm * ell ^ (1 / 16 : ℝ) / r ^ 2) := by
  obtain ⟨Dp, Dm, hDp, hDm, hFixed⟩ := actual_inner_fixed_Fredholm_moment_constants
  let K : ℝ := actualHartreePhysicalWeightedSourceConstant B A
  let T : ℝ := |actualHartreePhysicalChargeTailConstant|
  let L : ℝ := ‖criticalTailL2‖
  have hK : 0 ≤ K := actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA
  have hT : 0 ≤ T := abs_nonneg _
  have hL : 0 ≤ L := norm_nonneg _
  have hpModel := hPlusAffineSource_inWeightedL2 (7 / 4 : ℝ) (by norm_num)
  have hmModel := phaseAffineSource_inWeightedL2 (7 / 4 : ℝ) (by norm_num)
  let Ap : ℝ := ‖weightedSourceDataL2 (7 / 4 : ℝ)
    (channelAffineSource HartreeChannel.plus) hpModel‖
  let Am : ℝ := ‖weightedSourceDataL2 (7 / 4 : ℝ)
    (channelAffineSource HartreeChannel.minus) hmModel‖
  have hAp : 0 ≤ Ap := norm_nonneg _
  have hAm : 0 ≤ Am := norm_nonneg _
  let Sp : ℝ := 2 * K * L + 4 * K * T * Ap
  let Sm : ℝ := 2 * K * L + 2 * K * T * Am
  have hSp : 0 ≤ Sp := by dsimp [Sp]; positivity
  have hSm : 0 ≤ Sm := by dsimp [Sm]; positivity
  refine ⟨Dp * Sp, Dm * Sm, mul_nonneg hDp hSp, mul_nonneg hDm hSm, ?_⟩
  intro ell c hell hellOne hc z hz hSup hStrauss
  let e : ℝ := ell ^ (1 / 16 : ℝ)
  have he : 0 ≤ e := Real.rpow_nonneg hell.le _
  let G := actualHartreeRadiallyConjugatedInnerSource
    (actualHartreeSlowInnerRadius ell) ell c z
  let gp : ℝ → ℝ := fun r => (G r).re
  let gm : ℝ → ℝ := fun r => (G r).im
  have hSource := actual_Hartree_conjugated_slow_inner_one_sixteenth
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hPair := actual_Hartree_one_complex_weighted_source_two_channels
    (7 / 4 : ℝ) G hSource.1 hSource.2.1
  have hp : InWeightedL2 (7 / 4 : ℝ) gp := hPair.1
  have hm : InWeightedL2 (7 / 4 : ℝ) gm := hPair.2
  have hData (f : ℝ → ℝ) (hf : InWeightedL2 (7 / 4 : ℝ) f)
      (hNorm : ∀ r : ℝ, |f r| ≤ ‖G r‖) :
      ‖weightedSourceDataL2 (7 / 4 : ℝ) f hf‖ ≤ (2 * K * L) * e := by
    have h := sourceData_norm_of_envelope f hf ((2 * K) * e) (by
      intro r hr
      have hw : 0 ≤ affineJapaneseWeight (7 / 4 : ℝ) r := by
        unfold affineJapaneseWeight
        positivity
      exact (mul_le_mul_of_nonneg_left (hNorm r) hw).trans (hSource.2.2 r hr))
    exact h.trans_eq (by dsimp [L]; ring)
  have hpData := hData gp hp (fun r => Complex.abs_re_le_norm (G r))
  have hmData := hData gm hm (fun r => Complex.abs_im_le_norm (G r))
  have hCharges := actual_Hartree_conjugated_inner_forced_charges_one_sixteenth
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hpCharge : |actualPlusCharge gp| ≤ (4 * K * T) * e := by
    calc
      _ ≤ 2 * ((2 * K) * e * actualHartreePhysicalChargeTailConstant) := hCharges.1
      _ = (4 * K * e) * actualHartreePhysicalChargeTailConstant := by ring
      _ ≤ (4 * K * e) * T := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = (4 * K * T) * e := by ring
  have hmCharge : |actualMinusCharge gm| ≤ (2 * K * T) * e := by
    calc
      _ ≤ (2 * K) * e * actualHartreePhysicalChargeTailConstant := hCharges.2
      _ ≤ (2 * K) * e * T := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = (2 * K * T) * e := by ring
  have hpCorr := correctedPlusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) gp hp
  have hmCorr := correctedMinusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) gm hm
  have hpNorm : ‖weightedSourceDataL2 (7 / 4 : ℝ) (correctedPlusSource gp) hpCorr‖ ≤ Sp * e := by
    have h := correctedData_norm_le gp (channelAffineSource HartreeChannel.plus)
      (actualPlusCharge gp) hp hpModel hpCorr
    exact (h.trans (add_le_add hpData
      (mul_le_mul_of_nonneg_right hpCharge hAp))).trans_eq (by dsimp [Sp]; ring)
  have hmNorm : ‖weightedSourceDataL2 (7 / 4 : ℝ) (correctedMinusSource gm) hmCorr‖ ≤ Sm * e := by
    have h := correctedData_norm_le gm (channelAffineSource HartreeChannel.minus)
      (actualMinusCharge gm) hm hmModel hmCorr
    exact (h.trans (add_le_add hmData
      (mul_le_mul_of_nonneg_right hmCharge hAm))).trans_eq (by dsimp [Sm]; ring)
  obtain ⟨x, hx, _hunique⟩ := existsUnique_actualInner_affinelyCorrected
    (7 / 4 : ℝ) (by norm_num) (by norm_num) gp gm hp hm
  have hMom := hFixed (correctedPlusSource gp) (correctedMinusSource gm)
    hpCorr hmCorr x hx.1 hx.2
  have hMp : innerGreenBound (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
      (correctedPlusSource gp) ≤ (Dp * Sp) * e :=
    (hMom.1.trans (mul_le_mul_of_nonneg_left hpNorm hDp)).trans_eq (by ring)
  have hMm : innerGreenBound ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
      (correctedMinusSource gm) ≤ (Dm * Sm) * e :=
    (hMom.2.trans (mul_le_mul_of_nonneg_left hmNorm hDm)).trans_eq (by ring)
  refine ⟨hp, hm, x, hx.1, hx.2, hMp, hMm, ?_⟩
  intro r hr
  have hr0 : 0 ≤ r := by linarith
  have htp := innerGreenRepresentative_affine_physical_trace_bounds
    (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
    (7 / 4 : ℝ) (by norm_num) (correctedPlusSource gp) hpCorr
    (actualPlusCharge gp) r hr
  have htm := innerGreenRepresentative_affine_physical_trace_bounds
    ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
    (7 / 4 : ℝ) (by norm_num) (correctedMinusSource gm) hmCorr
    (actualMinusCharge gm) r hr
  exact ⟨htp.1.trans (div_le_div_of_nonneg_right hMp hr0),
    htp.2.trans (div_le_div_of_nonneg_right hMp (sq_nonneg r)),
    htm.1.trans (div_le_div_of_nonneg_right hMm hr0),
    htm.2.trans (div_le_div_of_nonneg_right hMm (sq_nonneg r))⟩

end HBL.TypeIIDynamicSelection
