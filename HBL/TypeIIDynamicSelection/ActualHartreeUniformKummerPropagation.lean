import HBL.TypeIIDynamicSelection.ActualHartreeCanonicalKummerTransfer
import HBL.TypeIIDynamicSelection.ActualKummerUniformSameSourceTransfer

/-!
Same actual Hartree source, same normalized Fredholm solution, same forced
complex affine charge: the scaled Kummer transfer no longer carries a
radius-dependent fundamental-pair amplification. The only geometric condition
is the explicit dyadic annulus ratio. Remote outgoing compatibility and the
complete iterated PDE residual are not asserted by this theorem.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

private theorem pair_norm_le (a b : ℝ) :
    ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ≤ |a| + |b| := by
  calc
    _ ≤ ‖(a : ℂ)‖ + ‖Complex.I * (b : ℂ)‖ := norm_add_le _ _
    _ = _ := by simp [Complex.norm_real, Real.norm_eq_abs]

private theorem physical_differentiableAt
    (g : RealL2 halfLineMeasure) (F : ℝ → ℝ)
    (hF : InWeightedL2 (7 / 4 : ℝ) F) (a r : ℝ) (hr : 0 < r) :
    DifferentiableAt ℝ
      (fun t : ℝ => affineRestore (innerGreenRepresentative g F) a t / t) r := by
  obtain ⟨h0, _h1, hEq, _hM⟩ :=
    innerGreenRepresentative_total_source_firstMoment g (7 / 4 : ℝ) (by norm_num) F hF
  have hG : DifferentiableAt ℝ (innerGreenRepresentative g F) r := by
    rw [hEq]
    exact ((halfLineMinGreen_C1_of_integrable _ h0).1 r).differentiableAt
  have hModel : DifferentiableAt ℝ model r :=
    ((contDiff_infty_iff_deriv.mp model_contDiff_infty).1 r)
  have hRest : DifferentiableAt ℝ (affineRestore (innerGreenRepresentative g F) a) r :=
    hG.add (hModel.const_mul a)
  exact hRest.div differentiableAt_id hr.ne'

/-- The actual canonical two-channel Hartree correction propagates through
the original Kummer annulus with a radius-INDEPENDENT coefficient. The
forcing cancels only as the exact difference of two transfers with the same
physical source. The affine-charge reference (alpha,0) is not discarded. -/
theorem actual_Hartree_canonical_inner_to_uniform_Kummer_transfer
    (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ Cp Cm : ℝ, 0 ≤ Cp ∧ 0 ≤ Cm ∧
    ∀ (ell c : ℝ) (_hell : 0 < ell) (_hellOne : ell ≤ 1) (_hc : |c| ≤ 1)
      (z : ℝ → ℂ) (_hz : Measurable z)
      (_hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
      (_hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A),
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
      (let up : ℝ → ℝ := fun r =>
          affineRestore (innerGreenRepresentative
            (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
            (correctedPlusSource gp)) (actualPlusCharge gp) r / r
       let um : ℝ → ℝ := fun r =>
          affineRestore (innerGreenRepresentative
            ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
            (correctedMinusSource gm)) (actualMinusCharge gm) r / r
       let alpha : ℂ := (actualPlusCharge gp : ℂ) +
          Complex.I * (actualMinusCharge gm : ℂ)
       ∀ (mu theta center eps : ℝ) (K : LocalKummerPair mu theta center eps)
         (d : ℝ), 0 < d → d < eps → 2 < center - d →
         center + d ≤ 2 * (center - d) →
         let r := center - d
         let U : ℂ := (up r : ℂ) + Complex.I * (um r : ℂ)
         let DU : ℂ := ((deriv up r : ℝ) : ℂ) +
           Complex.I * ((deriv um r : ℝ) : ℂ)
         let F := actualHartreePhysicalSliceInteraction ell c z
         HasDerivAt up (deriv up r) r ∧
         HasDerivAt um (deriv um r) r ∧
         max
           ‖(actualKummerPhysicalRightTransfer K d F U DU).1 -
             (actualKummerPhysicalRightTransfer K d F alpha 0).1‖
           ((center + d) * ‖(actualKummerPhysicalRightTransfer K d F U DU).2 -
             (actualKummerPhysicalRightTransfer K d F alpha 0).2‖) ≤
           actualKummerUniformTransferConstant (frozenZeroCoeff mu theta) *
             ((Cp + Cm) * ell ^ (1 / 16 : ℝ) / r)) := by
  obtain ⟨Cp, Cm, hCp, hCm, hUniform⟩ :=
    actual_Hartree_uniform_canonical_inner_moments_and_traces B A hB hA
  refine ⟨Cp, Cm, hCp, hCm, ?_⟩
  intro ell c hell hellOne hc z hz hSup hStrauss
  obtain ⟨hp, hm, x, hxp, hxm, _hMp, _hMm, hTrace⟩ :=
    hUniform ell c hell hellOne hc z hz hSup hStrauss
  refine ⟨hp, hm, x, hxp, hxm, ?_⟩
  dsimp only
  intro mu theta center eps K d hd hde hr hRatio
  let G := actualHartreeRadiallyConjugatedInnerSource
    (actualHartreeSlowInnerRadius ell) ell c z
  let gp : ℝ → ℝ := fun r => (G r).re
  let gm : ℝ → ℝ := fun r => (G r).im
  let up : ℝ → ℝ := fun r => affineRestore (innerGreenRepresentative
    (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
    (correctedPlusSource gp)) (actualPlusCharge gp) r / r
  let um : ℝ → ℝ := fun r => affineRestore (innerGreenRepresentative
    ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
    (correctedMinusSource gm)) (actualMinusCharge gm) r / r
  let r : ℝ := center - d
  let U : ℂ := (up r : ℂ) + Complex.I * (um r : ℂ)
  let DU : ℂ := ((deriv up r : ℝ) : ℂ) + Complex.I * ((deriv um r : ℝ) : ℂ)
  let alpha : ℂ := (actualPlusCharge gp : ℂ) + Complex.I * (actualMinusCharge gm : ℂ)
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hpCorr := correctedPlusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) gp hp
  have hmCorr := correctedMinusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) gm hm
  have hdp : HasDerivAt up (deriv up r) r :=
    (physical_differentiableAt _ _ hpCorr (actualPlusCharge gp) r hr0).hasDerivAt
  have hdm : HasDerivAt um (deriv um r) r :=
    (physical_differentiableAt _ _ hmCorr (actualMinusCharge gm) r hr0).hasDerivAt
  obtain ⟨hpVal, hpDer, hmVal, hmDer⟩ := hTrace r hr
  have hUeq : U - alpha =
      ((up r - actualPlusCharge gp : ℝ) : ℂ) +
        Complex.I * ((um r - actualMinusCharge gm : ℝ) : ℂ) := by
    dsimp [U, alpha]
    push_cast
    ring
  have hVal : ‖U - alpha‖ ≤ (Cp + Cm) * ell ^ (1 / 16 : ℝ) / r := by
    rw [hUeq]
    calc
      _ ≤ |up r - actualPlusCharge gp| + |um r - actualMinusCharge gm| := pair_norm_le _ _
      _ ≤ Cp * ell ^ (1 / 16 : ℝ) / r + Cm * ell ^ (1 / 16 : ℝ) / r :=
        _root_.add_le_add hpVal hmVal
      _ = _ := by ring
  have hDer : ‖DU - 0‖ ≤ (Cp + Cm) * ell ^ (1 / 16 : ℝ) / r ^ 2 := by
    rw [sub_zero]
    calc
      _ ≤ |deriv up r| + |deriv um r| := pair_norm_le _ _
      _ ≤ Cp * ell ^ (1 / 16 : ℝ) / r ^ 2 + Cm * ell ^ (1 / 16 : ℝ) / r ^ 2 :=
        _root_.add_le_add hpDer hmDer
      _ = _ := by ring
  have hScaledDer : r * ‖DU - 0‖ ≤ (Cp + Cm) * ell ^ (1 / 16 : ℝ) / r := by
    calc
      _ ≤ r * ((Cp + Cm) * ell ^ (1 / 16 : ℝ) / r ^ 2) :=
        mul_le_mul_of_nonneg_left hDer hr0.le
      _ = _ := by field_simp [hr0.ne']
  have hJet := max_le hVal hScaledDer
  have hTransfer := actual_Kummer_same_source_scaled_transfer_uniform
    K d hd hde hRatio (actualHartreePhysicalSliceInteraction ell c z) U DU alpha 0
  have hC : 0 ≤ actualKummerUniformTransferConstant (frozenZeroCoeff mu theta) := by
    unfold actualKummerUniformTransferConstant
    positivity
  exact ⟨hdp, hdm, hTransfer.trans (mul_le_mul_of_nonneg_left hJet hC)⟩

end HBL.TypeIIDynamicSelection
