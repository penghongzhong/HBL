import HBL.PhysicalRadial3PhaseCore
import HBL.AffineTailMinusAsymptotics
import HBL.AffineTailMinusZeroMode
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Identify the actual phase kernel with the stationary bubble W, rather
than with an unnamed singular vector. The input vector is the existing
fullBubbleRadialEnergyL2, represented by (r W)'=(1+r^2)^(-3/2).
The Gram identity is obtained from the actual adjoint tail integral and
the explicit derivative of (r W)'. No spectral or kernel assertion is
assumed about W. The final physical core gap uses the original bubble
energy pairing. Full Sobolev completion and the real nonlocal channel
remain outside the scope of this module.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem phaseBubble_ae :
    (fullBubbleRadialEnergyL2 : ℝ → ℝ) =ᵐ[halfLineMeasure]
      bubbleRadialEnergyDerivative :=
  bubbleRadialEnergyDerivative_memLp.coeFn_toLp

private theorem phaseBubble_image_ae :
    (weightedVolterraOperator fullBubbleRadialEnergyL2 : ℝ → ℝ) =ᵐ[
      halfLineMeasure] fun r => weightedGreenDecay r * radialU bubble r := by
  have h := weightedVolterraOperator_smoothToRadialDotH1_ae
    bubble bubble_contDiff radialU_bubble_deriv_memLp
  rw [smoothBubbleToRadialDotH1_eq] at h
  exact h

private def phaseBubbleSource (r : ℝ) : ℝ :=
  weightedGreenDecay r ^ 2 * radialU bubble r

private theorem phaseBubble_source_integrable :
    Integrable phaseBubbleSource halfLineMeasure := by
  apply (weightedGreen_source_integrable
    (weightedVolterraOperator fullBubbleRadialEnergyL2)).congr
  filter_upwards [phaseBubble_image_ae] with r hr
  rw [hr]
  dsimp [phaseBubbleSource]
  ring

private theorem phaseBubble_primitive_hasDerivAt (r : ℝ) :
    HasDerivAt (fun t => -(1 / 3 : ℝ) * bubbleRadialEnergyDerivative t)
      (phaseBubbleSource r) r := by
  have hsne : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hs4 : (1 + r ^ 2) ^ 2 = Real.sqrt (1 + r ^ 2) ^ 4 := by
    calc
      (1 + r ^ 2) ^ 2 = (Real.sqrt (1 + r ^ 2) ^ 2) ^ 2 := by rw [hs2]
      _ = Real.sqrt (1 + r ^ 2) ^ 4 := by ring
  apply ((bubbleRadialEnergyDerivative_hasDerivAt_closed r).const_mul
    (-(1 / 3 : ℝ))).congr_deriv
  dsimp [phaseBubbleSource, weightedGreenDecay, radialU, bubble,
    resonanceMinusSecondDerivative]
  rw [inv_pow, hs4]
  field_simp [hsne]

private theorem phaseBubble_derivative_tendsto_zero :
    Tendsto bubbleRadialEnergyDerivative atTop (𝓝 (0 : ℝ)) := by
  have hlim : Tendsto
      (fun r : ℝ => (resonanceMinus r * r⁻¹) ^ 3) atTop (𝓝 (0 : ℝ)) := by
    simpa using (resonanceMinus_tendsto_one.mul tendsto_inv_atTop_zero).pow 3
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hsne : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  dsimp [resonanceMinus, radialResonanceMinus, bubble, bubbleRadialEnergyDerivative]
  field_simp [ne_of_gt hr, hsne]

private theorem phaseBubble_source_tail (s : ℝ) (hs : 0 ≤ s) :
    (∫ r in Ioi s, phaseBubbleSource r) =
      (1 / 3 : ℝ) * bubbleRadialEnergyDerivative s := by
  have hfull : IntegrableOn phaseBubbleSource (Ioi (0 : ℝ)) :=
    phaseBubble_source_integrable
  have hint : IntegrableOn phaseBubbleSource (Ioi s) :=
    hfull.mono_set (Ioi_subset_Ioi hs)
  have hlim : Tendsto
      (fun r => -(1 / 3 : ℝ) * bubbleRadialEnergyDerivative r)
      atTop (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ℝ => -(1 / 3 : ℝ)) atTop
        (𝓝 (-(1 / 3 : ℝ))) := tendsto_const_nhds
    simpa only [mul_zero] using hc.mul phaseBubble_derivative_tendsto_zero
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (phaseBubble_primitive_hasDerivAt s).continuousAt.continuousWithinAt
    (fun r _ => phaseBubble_primitive_hasDerivAt r) hint hlim
  calc
    (∫ r in Ioi s, phaseBubbleSource r) =
        0 - (-(1 / 3 : ℝ) * bubbleRadialEnergyDerivative s) := h
    _ = (1 / 3 : ℝ) * bubbleRadialEnergyDerivative s := by ring

/-- The physical bubble energy coordinate is an actual Gram eigenvector. -/
theorem weightedVolterraGram_bubble :
    ContinuousLinearMap.adjoint weightedVolterraOperator
      (weightedVolterraOperator fullBubbleRadialEnergyL2) =
        (1 / 3 : ℝ) • fullBubbleRadialEnergyL2 := by
  apply Lp.ext
  filter_upwards [weightedVolterraOperator_adjoint_ae_pointwise
      (weightedVolterraOperator fullBubbleRadialEnergyL2),
    Lp.coeFn_smul (1 / 3 : ℝ) fullBubbleRadialEnergyL2,
    phaseBubble_ae, ae_restrict_mem measurableSet_Ioi] with s ha hm hb hs
  rw [ha, hm]
  change (∫ r in Ioi s,
      (1 + r ^ 2)⁻¹ * weightedVolterraOperator fullBubbleRadialEnergyL2 r) =
    (1 / 3 : ℝ) * fullBubbleRadialEnergyL2 s
  rw [hb]
  calc
    (∫ r in Ioi s,
        (1 + r ^ 2)⁻¹ * weightedVolterraOperator fullBubbleRadialEnergyL2 r) =
        ∫ r in Ioi s, phaseBubbleSource r := by
      apply integral_congr_ae
      have hlocal := ae_restrict_of_ae_restrict_of_subset
        (Ioi_subset_Ioi (show 0 ≤ s from le_of_lt hs)) phaseBubble_image_ae
      filter_upwards [hlocal] with r hr
      change (1 + r ^ 2)⁻¹ * weightedVolterraOperator fullBubbleRadialEnergyL2 r =
        phaseBubbleSource r
      rw [hr]
      dsimp [phaseBubbleSource, weightedGreenDecay]
      ring
    _ = (1 / 3 : ℝ) * bubbleRadialEnergyDerivative s :=
      phaseBubble_source_tail s (le_of_lt hs)

/-- The stationary bubble is a proved phase zero vector. -/
theorem weightedVolterraAMinus_bubble_zero :
    weightedVolterraAMinus fullBubbleRadialEnergyL2 = 0 := by
  change fullBubbleRadialEnergyL2 - (3 : ℝ) •
    (ContinuousLinearMap.adjoint weightedVolterraOperator
      (weightedVolterraOperator fullBubbleRadialEnergyL2)) = 0
  rw [weightedVolterraGram_bubble, smul_smul]
  norm_num

/-- The stationary bubble defines a nonzero energy vector. -/
theorem phaseBubble_energy_ne_zero : fullBubbleRadialEnergyL2 ≠ 0 := by
  intro hz
  have hae : bubbleRadialEnergyDerivative =ᵐ[halfLineMeasure] (0 : ℝ → ℝ) := by
    have hr := phaseBubble_ae
    rw [hz] at hr
    exact hr.symm.trans (Lp.coeFn_zero ℝ 2 halfLineMeasure)
  have hp := Measure.eqOn_open_of_ae_eq (μ := volume) hae isOpen_Ioi
    bubbleRadialEnergyDerivative_continuous.continuousOn continuous_zero.continuousOn
  have hzero : bubbleRadialEnergyDerivative 1 = 0 := hp (by norm_num)
  have hpos : 0 < bubbleRadialEnergyDerivative 1 := by
    unfold bubbleRadialEnergyDerivative
    positivity
  linarith

private theorem phaseBubble_firstMode_multiple :
    ∃ c : ℝ, c ≠ 0 ∧ c • weightedVolterraSineMode 0 = fullBubbleRadialEnergyL2 := by
  have hm : fullBubbleRadialEnergyL2 ∈ weightedVolterraAMinus.ker := by
    change weightedVolterraAMinus fullBubbleRadialEnergyL2 = 0
    exact weightedVolterraAMinus_bubble_zero
  rw [weightedVolterraAMinus_kernel_eq_sine_span] at hm
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz, zero_smul] at hc
  exact phaseBubble_energy_ne_zero hc.symm

/-- Exact phase-kernel identification with the physical stationary bubble. -/
theorem weightedVolterraAMinus_kernel_eq_bubble_span :
    weightedVolterraAMinus.ker = Submodule.span ℝ {fullBubbleRadialEnergyL2} := by
  obtain ⟨c, hc, hb⟩ := phaseBubble_firstMode_multiple
  rw [weightedVolterraAMinus_kernel_eq_sine_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' : x = weightedVolterraSineMode 0 := Set.mem_singleton_iff.mp hx
    subst x
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c⁻¹, ?_⟩
    rw [← hb, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' : x = fullBubbleRadialEnergyL2 := Set.mem_singleton_iff.mp hx
    subst x
    exact Submodule.mem_span_singleton.mpr ⟨c, hb⟩

/-- Orthogonality to the bubble is exactly orthogonality to the phase mode. -/
theorem phaseBubble_orthogonal_iff (x : RealL2 halfLineMeasure) :
    inner ℝ fullBubbleRadialEnergyL2 x = 0 ↔
      inner ℝ (weightedVolterraSineMode 0) x = 0 := by
  obtain ⟨c, hc, hb⟩ := phaseBubble_firstMode_multiple
  rw [← hb, real_inner_smul_left, mul_eq_zero]
  simp only [hc, false_or]

/-- The bubble energy pairing uses its explicit physical profile derivative. -/
theorem phaseBubble_coordinate_pairing (f : ℝ → ℝ)
    (hmem : MemLp (deriv (radialU f)) 2 halfLineMeasure) :
    inner ℝ fullBubbleRadialEnergyL2 (smoothToRadialDotH1 f hmem) =
      ∫ r : ℝ, bubbleRadialEnergyDerivative r * deriv (radialU f) r
        ∂halfLineMeasure := by
  rw [← smoothBubbleToRadialDotH1_eq,
    smoothRadialEnergy_coordinate_pairing]
  apply integral_congr_ae
  filter_upwards with r
  rw [radialU_bubble_deriv_closed]

/-- Physical core coercivity with the original bubble energy constraint. -/
theorem physicalRadial3_phase_core_bubble_coercive
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (R : ℝ) (hR : 0 ≤ R) (hcut : ∀ r : ℝ, R ≤ r → f r = 0)
    (hphase : (∫ r : ℝ, bubbleRadialEnergyDerivative r * deriv (radialU f) r
      ∂halfLineMeasure) = 0) :
    (4 / 5 : ℝ) * (∫ x : PhysicalRadialSpace3,
      ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) ≤
        physicalRadial3PhaseQuadratic f := by
  apply physicalRadial3_phase_core_coercive f hf R hR hcut
  apply (phaseBubble_orthogonal_iff _).mp
  rw [phaseBubble_coordinate_pairing]
  exact hphase

end HBL.Modulation.Monopole
