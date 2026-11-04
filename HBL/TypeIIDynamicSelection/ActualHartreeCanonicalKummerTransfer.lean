import HBL.TypeIIDynamicSelection.ActualHartreeUniformInnerMoment
import HBL.TypeIIDynamicSelection.ActualKummerSameSourceJetTransfer
import Mathlib.Tactic

/-!
Actual canonical Hartree inner traces feed the same-source Kummer transfer.
The normalized Fredholm equations and actual Green representatives are
retained. The reference Kummer solution retains the complex forced affine
charge, rather than replacing it by zero. The amplification of the moving
Kummer annulus is explicit; its scale-uniform control and the independent
remote compatibility conditions are NOT assumed or claimed here.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

private theorem complex_pair_norm_le (a b : ℝ) :
    ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ≤ |a| + |b| := by
  calc
    _ ≤ ‖(a : ℂ)‖ + ‖Complex.I * (b : ℂ)‖ := norm_add_le _ _
    _ = _ := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]

private theorem canonical_physical_differentiableAt
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
  exact hRest.div (differentiableAt_id) hr.ne'

/-- Constants are fixed BEFORE ell,c,z. Both canonical physical coordinate
traces are differentiable and the SAME original Hartree slice forcing is
retained in the two Kummer solutions. The result controls the transferred
perturbation of the forced-charge reference, not an arbitrary outer jet. -/
theorem actual_Hartree_canonical_inner_to_Kummer_transfer
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
         let r := center - d
         let U : ℂ := (up r : ℂ) + Complex.I * (um r : ℂ)
         let DU : ℂ := (deriv up r : ℂ) + Complex.I * (deriv um r : ℂ)
         let F := actualHartreePhysicalSliceInteraction ell c z
         HasDerivAt up (deriv up r) r ∧
         HasDerivAt um (deriv um r) r ∧
         localAnnulusWronskian K (-d) ≠ 0 ∧
         0 ≤ actualKummerJetAmplification K d ∧
         ‖(actualKummerPhysicalRightTransfer K d F U DU).1 -
             (actualKummerPhysicalRightTransfer K d F alpha 0).1‖ +
           ‖(actualKummerPhysicalRightTransfer K d F U DU).2 -
             (actualKummerPhysicalRightTransfer K d F alpha 0).2‖ ≤
           actualKummerJetAmplification K d *
             ((Cp + Cm) * ell ^ (1 / 16 : ℝ) / r +
               (Cp + Cm) * ell ^ (1 / 16 : ℝ) / r ^ 2)) := by
  obtain ⟨Cp, Cm, hCp, hCm, hUniform⟩ :=
    actual_Hartree_uniform_canonical_inner_moments_and_traces B A hB hA
  refine ⟨Cp, Cm, hCp, hCm, ?_⟩
  intro ell c hell hellOne hc z hz hSup hStrauss
  obtain ⟨hp, hm, x, hxp, hxm, _hMp, _hMm, hTrace⟩ :=
    hUniform ell c hell hellOne hc z hz hSup hStrauss
  refine ⟨hp, hm, x, hxp, hxm, ?_⟩
  dsimp only
  intro mu theta center eps K d hd hde hr
  dsimp only
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
  let DU : ℂ := (deriv up r : ℂ) + Complex.I * (deriv um r : ℂ)
  let alpha : ℂ := (actualPlusCharge gp : ℂ) + Complex.I * (actualMinusCharge gm : ℂ)
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hpCorr := correctedPlusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) gp hp
  have hmCorr := correctedMinusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) gm hm
  have hdp : HasDerivAt up (deriv up r) r :=
    (canonical_physical_differentiableAt _ _ hpCorr (actualPlusCharge gp) r hr0).hasDerivAt
  have hdm : HasDerivAt um (deriv um r) r :=
    (canonical_physical_differentiableAt _ _ hmCorr (actualMinusCharge gm) r hr0).hasDerivAt
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
      _ ≤ |up r - actualPlusCharge gp| + |um r - actualMinusCharge gm| :=
        complex_pair_norm_le _ _
      _ ≤ Cp * ell ^ (1 / 16 : ℝ) / r + Cm * ell ^ (1 / 16 : ℝ) / r :=
        _root_.add_le_add hpVal hmVal
      _ = _ := by ring
  have hDer : ‖DU - 0‖ ≤ (Cp + Cm) * ell ^ (1 / 16 : ℝ) / r ^ 2 := by
    rw [sub_zero]
    calc
      _ ≤ |deriv up r| + |deriv um r| := complex_pair_norm_le _ _
      _ ≤ Cp * ell ^ (1 / 16 : ℝ) / r ^ 2 + Cm * ell ^ (1 / 16 : ℝ) / r ^ 2 :=
        _root_.add_le_add hpDer hmDer
      _ = _ := by ring
  have hTransfer := actual_Kummer_same_source_right_transfer_norm_bound
    K d hd hde (actualHartreePhysicalSliceInteraction ell c z) U DU alpha 0
  exact ⟨hdp, hdm, hTransfer.1, hTransfer.2.1,
    hTransfer.2.2.trans
      (mul_le_mul_of_nonneg_left (_root_.add_le_add hVal hDer) hTransfer.2.1)⟩

end HBL.TypeIIDynamicSelection
