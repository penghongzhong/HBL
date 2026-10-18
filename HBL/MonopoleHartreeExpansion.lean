import HBL.MonopoleOuterCubic

/-! Actual integral-domain Taylor expansion for the truncated radial Hartree operator. -/

noncomputable section
open Set MeasureTheory
namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The actual radial Hartree nonlinearity; the potential already includes kappa. -/
def radialHartreeNonlinearity (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  radialHartreePotential (fun rho => u rho ^ 4) r * u r ^ 3

/-- The actual first variation on the truncated profile. -/
def monopoleRadialHartreeFirstVariation (R r : ℝ) : ℝ :=
  4 * radialHartreePotential (fun rho => bubble rho ^ 3 *
      monopoleInnerRadialProfile R rho) r * bubble r ^ 3 +
    3 * radialHartreePotential (fun rho => bubble rho ^ 4) r *
      bubble r ^ 2 * monopoleInnerRadialProfile R r

/-- Both convergence of the full perturbed fourth-power density and its
actual integral expansion follow from the established three component rows. -/
theorem monopoleHartreePotential_actual_expansion {c r : ℝ}
    (hc : 0 < |c|) (hc1 : |c| ≤ 1) (hr : 0 < r) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c rho ^ 4) (Ioi 0) ∧
    radialHartreePotential
      (fun rho => monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c rho ^ 4) r =
      radialHartreePotential (fun rho => bubble rho ^ 4) r +
      4 * c * radialHartreePotential (fun rho => bubble rho ^ 3 *
        monopoleInnerRadialProfile (monopoleQuadraticRadius c) rho) r +
      radialHartreePotential
        (monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c) r := by
  let R := monopoleQuadraticRadius c
  have hbase := monopoleHartreeBaseLinear_control (R := R) hr
  have hD := (monopoleHartreeDensityPotential_quadratic_control hc hc1 hr).1
  have he : (fun rho => rho * hartreeRadialLog r rho *
      monopolePerturbedRadialProfile R c rho ^ 4) =
      (fun rho => (rho * hartreeRadialLog r rho * bubble rho ^ 4 +
        (4 * c) * (rho * hartreeRadialLog r rho *
          (bubble rho ^ 3 * monopoleInnerRadialProfile R rho))) +
        rho * hartreeRadialLog r rho * monopoleHartreeDensityRemainder R c rho) := by
    funext rho
    unfold monopolePerturbedRadialProfile monopoleHartreeDensityRemainder
    ring
  have hint := (hbase.1.1.add (hbase.2.1.const_mul (4 * c))).add hD
  refine ⟨?_, ?_⟩
  · change IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
        monopolePerturbedRadialProfile R c rho ^ 4) (Ioi 0)
    rw [he]
    exact hint
  · change radialHartreePotential (fun rho => monopolePerturbedRadialProfile R c rho ^ 4) r = _
    unfold radialHartreePotential
    have htotal := integral_add (hbase.1.1.add (hbase.2.1.const_mul (4 * c))) hD
    have hmiddle := integral_add hbase.1.1 (hbase.2.1.const_mul (4 * c))
    simp only [Pi.add_apply, R] at htotal hmiddle
    rw [he]
    simp only [R]
    rw [htotal, hmiddle, integral_const_mul]
    ring

/-- An exact decomposition of the complete actual nonlinear Taylor error.
All potentials in this identity have established absolute convergence. -/
theorem monopoleRadialHartree_remainder_exact {c r : ℝ}
    (hc : 0 < |c|) (hc1 : |c| ≤ 1) (hr : 0 < r) :
    radialHartreeNonlinearity
        (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c) r -
      radialHartreeNonlinearity bubble r -
      c * monopoleRadialHartreeFirstVariation (monopoleQuadraticRadius c) r =
    radialHartreePotential
        (monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c) r *
      monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r ^ 3 +
    radialHartreePotential (fun rho => bubble rho ^ 4) r *
      (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r ^ 3 -
        bubble r ^ 3 - 3 * c * bubble r ^ 2 *
          monopoleInnerRadialProfile (monopoleQuadraticRadius c) r) +
    4 * c * radialHartreePotential (fun rho => bubble rho ^ 3 *
      monopoleInnerRadialProfile (monopoleQuadraticRadius c) rho) r *
      (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r ^ 3 - bubble r ^ 3) := by
  unfold radialHartreeNonlinearity monopoleRadialHartreeFirstVariation
  rw [(monopoleHartreePotential_actual_expansion hc hc1 hr).2]
  ring

end HBL.Modulation.Monopole
