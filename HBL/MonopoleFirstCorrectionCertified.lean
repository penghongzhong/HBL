import HBL.MonopoleProfileEquation

/-!
The complete first-correction statement for the revised manuscript Lemma 2.5.
The cutoff and Hilbert-orthogonal Fredholm solution are fixed by the actual
definitions. No uniqueness among arbitrary classical profiles or invariance
under changing the cutoff is asserted. The equation, classical regularity,
and both quantitative tails below are the interface used downstream.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole

open HBL.Modulation.AffineTail

/-- The fixed first correction solves the actual half-line equation and has
the explicit affine tail required by the inner/outer matching argument. -/
theorem monopole_first_correction_certified :
    (monopoleRemainder_weighted_memLp_two.toLp
      (fun r => weightedGreenDecay r * monopoleRemainder r) ∈
        (1 - weightedBirmanSchwingerOperator).kerᗮ) ∧
    Continuous monopoleProfile ∧
    monopoleProfile 0 = 0 ∧
    (∀ r : ℝ, 0 < r →
      DifferentiableAt ℝ monopoleProfile r ∧
      DifferentiableAt ℝ (deriv monopoleProfile) r ∧
      hPlusApply monopoleProfile r = r * bubble r ^ 3) ∧
    ContinuousOn (deriv (deriv monopoleProfile)) (Ioi (0 : ℝ)) ∧
    0 ≤ monopoleSourceDecayConstant ∧
    (∀ r : ℝ, 2 < r →
      |monopoleProfile r -
        (Real.log r - (Real.pi / 8) * r + monopoleTailConstant)| ≤
          monopoleSourceDecayConstant / r ∧
      |monopoleRadialProfile r -
        (-(Real.pi / 8) + (Real.log r + monopoleTailConstant) / r)| ≤
          monopoleSourceDecayConstant / r ^ 2) ∧
    Tendsto monopoleRadialProfile atTop (𝓝 (-(Real.pi / 8))) := by
  refine ⟨?_, monopoleProfile_continuous, monopoleProfile_zero, ?_,
    monopoleProfile_secondDeriv_continuousOn,
    monopoleSourceDecayConstant_nonneg, ?_,
    monopoleRadialProfile_tendsto_neg_pi_div_eight⟩
  · rw [monopoleRemainder_weighted_toLp]
    exact monopoleFredholmSolution.property
  · intro r hr
    refine ⟨(monopoleProfile_hasDerivAt hr).differentiableAt,
      (monopoleProfile_second_hasDerivAt hr).differentiableAt, ?_⟩
    simpa only [monopoleSource] using monopoleProfile_hPlus_equation hr
  · intro r hr
    constructor
    · simpa only [monopoleAffineSlope_eq_neg_pi_div_eight, neg_mul,
        sub_eq_add_neg] using monopoleProfile_sub_asymptotic_abs_le hr
    · simpa only [monopoleAffineSlope_eq_neg_pi_div_eight] using
        monopoleRadialProfile_sub_asymptotic_abs_le hr

end HBL.Modulation.Monopole
