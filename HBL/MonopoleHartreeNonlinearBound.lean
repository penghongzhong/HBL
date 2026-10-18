import HBL.MonopoleHartreeExpansion

/-! A genuine uniform quadratic estimate for the full radial Hartree Taylor remainder. -/

noncomputable section
open Set MeasureTheory
namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- An amplitude-independent constant for the complete actual truncated nonlinearity. -/
def monopoleHartreeNonlinearBoundConstant : ℝ :=
  monopoleHartreePotentialBoundConstant * (1 + monopoleRadialBoundConstant) ^ 3 +
  radialHartreeRowBoundConstant * monopoleOuterCubicTaylorConstant +
  4 * radialHartreeRowBoundConstant * monopoleRadialBoundConstant *
    monopoleOuterCubicDifferenceConstant

theorem monopoleHartreeNonlinearBoundConstant_pos :
    0 < monopoleHartreeNonlinearBoundConstant := by
  have hB := monopoleRadialBoundConstant_pos
  have hrow := radialHartreeRowBoundConstant_pos
  have hbub := radialHartreeBubbleBoundConstant_pos
  unfold monopoleHartreeNonlinearBoundConstant monopoleHartreePotentialBoundConstant
    monopoleHartreeDensityDecayConstant monopoleOuterCubicTaylorConstant
    monopoleOuterCubicDifferenceConstant hartreeKappa
  positivity

/-- The full actual radial nonlinear Taylor remainder is uniformly quadratic,
including the outer cubic factor. No terminal bound or integrability is assumed.
This concerns the actual truncated profile and does not assert the three-dimensional
conjugation bridge or the dynamic matching and threshold projections. -/
theorem monopoleRadialHartree_nonlinear_quadratic_control {c r : ℝ}
    (hc : 0 < |c|) (hc1 : |c| ≤ 1) (hr : 0 < r) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c rho ^ 4) (Ioi 0) ∧
    |radialHartreeNonlinearity
        (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c) r -
      radialHartreeNonlinearity bubble r -
      c * monopoleRadialHartreeFirstVariation (monopoleQuadraticRadius c) r| ≤
      monopoleHartreeNonlinearBoundConstant * c ^ 2 := by
  refine ⟨(monopoleHartreePotential_actual_expansion hc hc1 hr).1, ?_⟩
  have hB := monopoleRadialBoundConstant_pos.le
  have hrow := radialHartreeRowBoundConstant_pos.le
  have hbase := monopoleHartreeBaseLinear_control (R := monopoleQuadraticRadius c) hr
  have hD := (monopoleHartreeDensityPotential_quadratic_control hc hc1 hr).2
  have hU := monopolePerturbedRadialProfile_abs_le (R := monopoleQuadraticRadius c) hr hc1
  have hQ := monopoleOuterCubic_taylor_abs_le (R := monopoleQuadraticRadius c) hr hc1
  have hT := monopoleOuterCubic_difference_abs_le (R := monopoleQuadraticRadius c) hr hc1
  have hCD : 0 ≤ monopoleHartreePotentialBoundConstant := by
    have h := radialHartreeBubbleBoundConstant_pos.le
    unfold monopoleHartreePotentialBoundConstant monopoleHartreeDensityDecayConstant hartreeKappa
    positivity
  have hCQ : 0 ≤ monopoleOuterCubicTaylorConstant := by
    unfold monopoleOuterCubicTaylorConstant
    positivity
  have hCT : 0 ≤ monopoleOuterCubicDifferenceConstant := by
    unfold monopoleOuterCubicDifferenceConstant
    positivity
  rw [monopoleRadialHartree_remainder_exact hc hc1 hr]
  calc
    _ ≤ |radialHartreePotential
          (monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c) r *
        monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r ^ 3| +
      |radialHartreePotential (fun rho => bubble rho ^ 4) r *
        (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r ^ 3 -
          bubble r ^ 3 - 3 * c * bubble r ^ 2 *
            monopoleInnerRadialProfile (monopoleQuadraticRadius c) r)| +
      |4 * c * radialHartreePotential (fun rho => bubble rho ^ 3 *
        monopoleInnerRadialProfile (monopoleQuadraticRadius c) rho) r *
        (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r ^ 3 - bubble r ^ 3)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |radialHartreePotential
          (monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c) r| *
        |monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r| ^ 3 +
      |radialHartreePotential (fun rho => bubble rho ^ 4) r| *
        |monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r ^ 3 -
          bubble r ^ 3 - 3 * c * bubble r ^ 2 *
            monopoleInnerRadialProfile (monopoleQuadraticRadius c) r| +
      4 * |c| * |radialHartreePotential (fun rho => bubble rho ^ 3 *
        monopoleInnerRadialProfile (monopoleQuadraticRadius c) rho) r| *
        |monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r ^ 3 - bubble r ^ 3| := by
      simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    _ ≤ (monopoleHartreePotentialBoundConstant * c ^ 2) *
        (1 + monopoleRadialBoundConstant) ^ 3 +
      radialHartreeRowBoundConstant * (monopoleOuterCubicTaylorConstant * c ^ 2) +
      4 * |c| * (radialHartreeRowBoundConstant * monopoleRadialBoundConstant) *
        (monopoleOuterCubicDifferenceConstant * |c|) := by
      gcongr
      · exact hbase.1.2
      · exact hbase.2.2
    _ = monopoleHartreeNonlinearBoundConstant * c ^ 2 := by
      unfold monopoleHartreeNonlinearBoundConstant
      rw [← sq_abs c]
      ring

end HBL.Modulation.Monopole
