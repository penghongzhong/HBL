import HBL.AffineTailLogLocalIntegrability

/-!
Exact finite-cutoff assembly of the weighted rational term arising
in the logarithmic Hartree integration by parts.

All integrations are ordinary interval integrals and exclude the
singular radius rho=r by a strictly positive symmetric gap.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- Each finite gap splits the weighted derivative into two regular
integral pairs and the Cauchy-kernel integral pair. -/
theorem pv_weight_split_decomposition
    (r e R : ℝ) (hr : 0 < r) (he : 0 < e)
    (her : e < r) (hR : r + e ≤ R) :
    (∫ rho in (0 : ℝ)..(r - e),
        (2 * r / (r ^ 2 - rho ^ 2)) * radialLogPrimitive rho) +
      (∫ rho in (r + e)..R,
        (2 * r / (r ^ 2 - rho ^ 2)) * radialLogPrimitive rho) =
      (r / 2) *
        ((r ^ 2 / (1 + r ^ 2) ^ 2) *
          ((∫ rho in (0 : ℝ)..(r - e), (1 + rho ^ 2)⁻¹) +
            (∫ rho in (r + e)..R, (1 + rho ^ 2)⁻¹)) -
        (1 / (1 + r ^ 2)) *
          ((∫ rho in (0 : ℝ)..(r - e), ((1 + rho ^ 2) ^ 2)⁻¹) +
            (∫ rho in (r + e)..R, ((1 + rho ^ 2) ^ 2)⁻¹)) +
        (r ^ 2 / (1 + r ^ 2) ^ 2) *
          ((∫ rho in (0 : ℝ)..(r - e), (r ^ 2 - rho ^ 2)⁻¹) +
            (∫ rho in (r + e)..R, (r ^ 2 - rho ^ 2)⁻¹))) := by
  have h0 : (0 : ℝ) ≤ r - e := by linarith
  have hLeft : ∀ rho ∈ Set.uIcc (0 : ℝ) (r - e),
      r ^ 2 - rho ^ 2 ≠ 0 := by
    intro rho hx
    rw [Set.uIcc_of_le h0] at hx
    have hp : 0 < r + rho := by linarith [hx.1]
    have hm : 0 < r - rho := by linarith [hx.2]
    intro heq
    nlinarith [mul_pos hp hm]
  have hRight : ∀ rho ∈ Set.uIcc (r + e) R,
      r ^ 2 - rho ^ 2 ≠ 0 := by
    intro rho hx
    rw [Set.uIcc_of_le hR] at hx
    have hp : 0 < r + rho := by linarith [hx.1]
    have hm : r - rho < 0 := by linarith [hx.1]
    intro heq
    nlinarith [mul_neg_of_pos_of_neg hp hm]
  rw [pv_weight_interval_decomposition r 0 (r - e) hLeft,
    pv_weight_interval_decomposition r (r + e) R hRight]
  ring

end HBL.Modulation.AffineTail
