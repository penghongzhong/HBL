import HBL.ThresholdTestExistence

/-!
Final certification package for the manuscript's first numbered lemma.

The fixed tests are the explicit normalized smooth compact tests already
constructed in ThresholdTestExistence.  We specialize all abstract radii to
  S = 1, R0 = exp(1),
which contains the transported support throughout the local log-scale window.

The main theorem below packages:
* an arbitrary base bubble exp(i gamma0) W_{exp(a0)};
* a C1 absolute physical selector (lambda,gamma);
* lambda > 0;
* the two verified threshold constraints;
* local uniqueness in state-parameter space;
* phase independence under gamma -> gamma + 2*pi*n;
* the concrete standard-bubble Jacobian -I2.

A companion theorem records exact agreement with the manuscript's two scalar
threshold equations on every smooth finite-energy radial core state.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation

/-- The fixed outer radius used for the explicit compact threshold tests. -/
def firstModulationRadius : ℝ := Real.exp 1

theorem firstModulation_one_le_radius :
    (1 : ℝ) ≤ firstModulationRadius := by
  unfold firstModulationRadius
  exact (Real.one_lt_exp_iff.mpr (by norm_num)).le

theorem firstModulation_radius_nonneg :
    0 ≤ firstModulationRadius := by
  unfold firstModulationRadius
  exact (Real.exp_pos 1).le

/-- The explicit positive test vanishes at the fixed outer radius. -/
theorem normalizedZetaPlus_at_firstModulationRadius :
    normalizedZetaPlus firstModulationRadius = 0 :=
  normalizedZetaPlus_zero_of_one_le _
    firstModulation_one_le_radius

/-- C1 versions of the C-infinity explicit tests, used by the IFT layer. -/
theorem normalizedZetaPlus_contDiff_one :
    ContDiff ℝ 1 normalizedZetaPlus :=
  normalizedZetaPlus_contDiff_infty.of_le (by simp)

theorem normalizedZetaMinus_contDiff_one :
    ContDiff ℝ 1 normalizedZetaMinus :=
  normalizedZetaMinus_contDiff_infty.of_le (by simp)

/-- Exact agreement between the fully verified Hilbert residual and the two
manuscript threshold equations on smooth finite-energy radial data. -/
theorem firstManuscriptModulation_residual_on_smoothCore
    (uRe uIm : ℝ → ℝ)
    (huRe : ContDiff ℝ 1 uRe)
    (huIm : ContDiff ℝ 1 uIm)
    (hmemRe : MemLp (deriv (radialU uRe)) 2
      (volume.restrict (Ioi (0 : ℝ))))
    (hmemIm : MemLp (deriv (radialU uIm)) 2
      (volume.restrict (Ioi (0 : ℝ))))
    (a₀ gamma₀ : ℝ) (p : Param)
    (hp : 0 < p.1)
    (hb : Real.log p.1 - a₀ ∈ Icc (-1 : ℝ) 1) :
    phasedAbsoluteResidual
      firstModulationRadius firstModulation_radius_nonneg
      normalizedZetaPlus normalizedZetaMinus
      normalizedZetaPlus_contDiff_one normalizedZetaMinus_contDiff_one
      a₀ gamma₀
      (smoothToRadialDotH1 uRe hmemRe,
        smoothToRadialDotH1 uIm hmemIm) p =
    manuscriptSmoothResidual
      1 normalizedZetaPlus normalizedZetaMinus
      uRe uIm (Real.log p.1) p.2 := by
  apply phasedAbsoluteResidual_on_smoothCore_eq_manuscript
    1 firstModulationRadius (by norm_num)
    firstModulation_radius_nonneg
    (by simp [firstModulationRadius])
    normalizedZetaPlus normalizedZetaMinus
    normalizedZetaPlus_contDiff_one normalizedZetaMinus_contDiff_one
    normalizedZetaPlus_zero_of_one_le
    normalizedZetaMinus_zero_of_one_le
    uRe uIm huRe huIm hmemRe hmemIm
    a₀ gamma₀ p hp hb

/-- Concrete standard-bubble Jacobian for the explicit fixed tests. -/
theorem firstManuscriptModulation_standardJacobian :
    (fderiv ℝ
      (scalePhaseResidual
        (fullTransportedEnergyThresholdDual
          firstModulationRadius firstModulation_radius_nonneg
          normalizedZetaPlus normalizedZetaPlus_contDiff_one)
        (fullTransportedEnergyThresholdDual
          firstModulationRadius firstModulation_radius_nonneg
          normalizedZetaMinus normalizedZetaMinus_contDiff_one)
        fullBubbleRadialEnergyL2)
      ((fullBubbleRadialEnergyL2, (0 : RadialDotH1)),
        (0 : Param))).comp
      (ContinuousLinearMap.inr ℝ ComplexRadialDotH1 Param) =
        parameterNegId := by
  exact manuscript_standardBubble_jacobian_eq_negId
    firstModulationRadius firstModulation_radius_nonneg
    normalizedZetaPlus normalizedZetaMinus
    normalizedZetaPlus_contDiff_one normalizedZetaMinus_contDiff_one
    normalizedZetaPlus_at_firstModulationRadius
    (by
      simpa [firstModulationRadius] using normalizedZetaPlus_normalized)
    (by
      simpa [firstModulationRadius] using normalizedZetaMinus_normalized)

/-- Final certified local modulation theorem at an arbitrary phased/scaled
bubble.  The uniqueness clause is the local state-parameter uniqueness
delivered by the finite-dimensional implicit-function theorem. -/
theorem firstManuscriptModulationLemma_certified
    (a₀ gamma₀ : ℝ) :
    ∃ LambdaGamma : ComplexRadialDotH1 → Param,
      LambdaGamma (phasedBubbleRadialDotH1 a₀ gamma₀) =
        (Real.exp a₀, gamma₀) ∧
      ContDiffAt ℝ 1 LambdaGamma
        (phasedBubbleRadialDotH1 a₀ gamma₀) ∧
      (∀ u, 0 < (LambdaGamma u).1) ∧
      (∀ᶠ u in 𝓝 (phasedBubbleRadialDotH1 a₀ gamma₀),
        phasedAbsoluteResidual
          firstModulationRadius firstModulation_radius_nonneg
          normalizedZetaPlus normalizedZetaMinus
          normalizedZetaPlus_contDiff_one normalizedZetaMinus_contDiff_one
          a₀ gamma₀ u (LambdaGamma u) = 0) ∧
      (∀ᶠ v in 𝓝
        (phasedBubbleRadialDotH1 a₀ gamma₀,
          (Real.exp a₀, gamma₀)),
        0 < v.2.1 →
          (phasedAbsoluteResidual
            firstModulationRadius firstModulation_radius_nonneg
            normalizedZetaPlus normalizedZetaMinus
            normalizedZetaPlus_contDiff_one normalizedZetaMinus_contDiff_one
            a₀ gamma₀ v.1 v.2 = 0 ↔
            LambdaGamma v.1 = v.2)) ∧
      (∀ (u : ComplexRadialDotH1) (n : ℤ),
        phaseClass
          ((LambdaGamma u).2 + (n : ℝ) * (2 * Real.pi)) =
        phaseClass (LambdaGamma u).2) := by
  obtain ⟨LambdaGamma, hbase, hC1, hpos, hsolve, hunique⟩ :=
    manuscript_modulation_local_corrected
      1 firstModulationRadius (by norm_num)
      firstModulation_radius_nonneg
      firstModulation_one_le_radius
      (by simp [firstModulationRadius])
      normalizedZetaPlus normalizedZetaMinus
      normalizedZetaPlus_contDiff_one normalizedZetaMinus_contDiff_one
      normalizedZetaPlus_zero_of_one_le
      normalizedZetaMinus_zero_of_one_le
      (by simpa [firstModulationRadius] using normalizedZetaPlus_normalized)
      (by simpa [firstModulationRadius] using normalizedZetaMinus_normalized)
      a₀ gamma₀
  refine ⟨LambdaGamma, hbase, hC1, hpos, hsolve, hunique, ?_⟩
  intro u n
  exact phaseClass_add_int_two_pi (LambdaGamma u).2 n

/-- One object bundles all manuscript-level obligations for the first
numbered lemma: explicit threshold tests exist, the arbitrary-bubble local
chart is certified, and the standard-bubble Jacobian is -I2. -/
theorem firstManuscriptModulationEnvironment_closed
    (a₀ gamma₀ : ℝ) :
    (∃ LambdaGamma : ComplexRadialDotH1 → Param,
      LambdaGamma (phasedBubbleRadialDotH1 a₀ gamma₀) =
        (Real.exp a₀, gamma₀) ∧
      ContDiffAt ℝ 1 LambdaGamma
        (phasedBubbleRadialDotH1 a₀ gamma₀) ∧
      (∀ u, 0 < (LambdaGamma u).1) ∧
      (∀ᶠ u in 𝓝 (phasedBubbleRadialDotH1 a₀ gamma₀),
        phasedAbsoluteResidual
          firstModulationRadius firstModulation_radius_nonneg
          normalizedZetaPlus normalizedZetaMinus
          normalizedZetaPlus_contDiff_one normalizedZetaMinus_contDiff_one
          a₀ gamma₀ u (LambdaGamma u) = 0) ∧
      (∀ᶠ v in 𝓝
        (phasedBubbleRadialDotH1 a₀ gamma₀,
          (Real.exp a₀, gamma₀)),
        0 < v.2.1 →
          (phasedAbsoluteResidual
            firstModulationRadius firstModulation_radius_nonneg
            normalizedZetaPlus normalizedZetaMinus
            normalizedZetaPlus_contDiff_one normalizedZetaMinus_contDiff_one
            a₀ gamma₀ v.1 v.2 = 0 ↔
            LambdaGamma v.1 = v.2)) ∧
      (∀ (u : ComplexRadialDotH1) (n : ℤ),
        phaseClass
          ((LambdaGamma u).2 + (n : ℝ) * (2 * Real.pi)) =
        phaseClass (LambdaGamma u).2)) ∧
    ((fderiv ℝ
      (scalePhaseResidual
        (fullTransportedEnergyThresholdDual
          firstModulationRadius firstModulation_radius_nonneg
          normalizedZetaPlus normalizedZetaPlus_contDiff_one)
        (fullTransportedEnergyThresholdDual
          firstModulationRadius firstModulation_radius_nonneg
          normalizedZetaMinus normalizedZetaMinus_contDiff_one)
        fullBubbleRadialEnergyL2)
      ((fullBubbleRadialEnergyL2, (0 : RadialDotH1)),
        (0 : Param))).comp
      (ContinuousLinearMap.inr ℝ ComplexRadialDotH1 Param) =
        parameterNegId) := by
  exact ⟨firstManuscriptModulationLemma_certified a₀ gamma₀,
    firstManuscriptModulation_standardJacobian⟩

end HBL.Modulation
