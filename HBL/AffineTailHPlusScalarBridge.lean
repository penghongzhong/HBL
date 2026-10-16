import HBL.TransversalityExact

/-!
The exact scalar formula sufficient for the real-channel zero mode.
No new mathematical hypothesis is hidden: the premise states the one
remaining one-dimensional improper integral with its proposed closed form.
The algebraic implication to H_plus psi_plus = 0 is proved below.
-/

noncomputable section

namespace HBL.Modulation.AffineTail

/-- The value of the one-dimensional logarithmic integral needed in H-plus. -/
def affineLogIntegralExpected (r : ℝ) : ℝ :=
  Real.pi * r * (1 - r ^ 2) / (8 * (1 + r ^ 2) ^ 2)

/-- Exact equality of the predicted nonlocal term and the checked
local differential residual. -/
theorem hPlus_scalar_match (r : ℝ) :
    (8 * Real.pi * hartreeKappa * bubble r ^ 3) *
        affineLogIntegralExpected r =
      3 * potential r * resonanceMinus r +
        r * potentialDerivative r * resonanceMinus r -
        2 * r * potential r * deriv resonanceMinus r := by
  have hd : deriv resonanceMinus r = bubbleRadialEnergyDerivative r := by
    change deriv (radialU bubble) r = bubbleRadialEnergyDerivative r
    exact radialU_bubble_deriv_closed r
  rw [hd, resonanceMinus_def]
  have hs : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hs4 : (1 + r ^ 2) ^ 2 = Real.sqrt (1 + r ^ 2) ^ 4 := by
    calc
      (1 + r ^ 2) ^ 2 = (Real.sqrt (1 + r ^ 2) ^ 2) ^ 2 := by rw [hs2]
      _ = Real.sqrt (1 + r ^ 2) ^ 4 := by ring
  have hs6 : (1 + r ^ 2) ^ 3 = Real.sqrt (1 + r ^ 2) ^ 6 := by
    calc
      (1 + r ^ 2) ^ 3 = (Real.sqrt (1 + r ^ 2) ^ 2) ^ 3 := by rw [hs2]
      _ = Real.sqrt (1 + r ^ 2) ^ 6 := by ring
  unfold affineLogIntegralExpected hartreeKappa potential potentialDerivative
    bubble bubbleRadialEnergyDerivative
  rw [hs4, hs6]
  field_simp [hs, Real.pi_ne_zero]
  nlinarith [hs2]

/-- Once the explicit one-dimensional integral is evaluated, the precise
real-channel Hartree zero mode follows. This is a reduction, not an
assertion that the integral is already evaluated. -/
theorem hPlus_zero_of_affineLogIntegral_expected
    (hint : ∀ r : ℝ, 0 < r →
      affineLogIntegral r = affineLogIntegralExpected r) :
    ∀ r : ℝ, 0 < r → hPlusApply resonancePlus r = 0 := by
  apply hPlus_zero_of_nonlocal_formula
  intro r hr
  rw [nonlocalApply_resonancePlus_factor r, hint r hr]
  exact hPlus_scalar_match r

end HBL.Modulation.AffineTail
