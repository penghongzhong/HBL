import HBL.AffineTailOperators

/-!
Explicit zero-mode calculation for the local H_- channel.

For
  psi_-(r)=r/sqrt(1+r^2),
we verify its first and second derivatives and then directly prove
  (-d^2/dr^2 - 3/(1+r^2)^2) psi_- = 0.
No spectral theorem is used in this calculation.
-/

noncomputable section

namespace HBL.Modulation.AffineTail

/-- Closed second derivative of the phase resonance. -/
def resonanceMinusSecondDerivative (r : ℝ) : ℝ :=
  -3 * r * (Real.sqrt (1 + r ^ 2) ^ 5)⁻¹

/-- Derivative of the already explicit first radial-energy derivative. -/
theorem bubbleRadialEnergyDerivative_hasDerivAt_closed (r : ℝ) :
    HasDerivAt bubbleRadialEnergyDerivative
      (resonanceMinusSecondDerivative r) r := by
  have hq :
      HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    have h :=
      (hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).pow 2)
    convert h using 1
    · funext x
      simp
    · norm_num
  have hqpos : 0 < (1 + r ^ 2 : ℝ) := by positivity
  have hspos : 0 < Real.sqrt (1 + r ^ 2) :=
    Real.sqrt_pos.2 hqpos
  have hsne : Real.sqrt (1 + r ^ 2) ≠ 0 :=
    ne_of_gt hspos
  have hs :
      HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2))
        (r / Real.sqrt (1 + r ^ 2)) r := by
    have hs0 := hq.sqrt (ne_of_gt hqpos)
    convert hs0 using 1
    field_simp [hsne]
  have hp := hs.pow 3
  have hi := hp.inv (pow_ne_zero 3 hsne)
  change HasDerivAt
    (fun x : ℝ => (Real.sqrt (1 + x ^ 2) ^ 3)⁻¹)
    (resonanceMinusSecondDerivative r) r
  convert hi using 1
  · unfold resonanceMinusSecondDerivative
    simp only [Pi.pow_apply]
    field_simp [hsne]
    ring

/-- The second derivative of the phase resonance has the closed form above. -/
theorem resonanceMinus_second_deriv_closed (r : ℝ) :
    deriv (deriv resonanceMinus) r =
      resonanceMinusSecondDerivative r := by
  have hfirst : deriv resonanceMinus = bubbleRadialEnergyDerivative := by
    funext x
    change deriv (radialU bubble) x = bubbleRadialEnergyDerivative x
    exact radialU_bubble_deriv_closed x
  rw [hfirst]
  exact (bubbleRadialEnergyDerivative_hasDerivAt_closed r).deriv

/-- Exact zero-energy equation in the imaginary channel. -/
theorem hMinus_resonanceMinus_zero (r : ℝ) :
    hMinusApply resonanceMinus r = 0 := by
  have hqpos : 0 < (1 + r ^ 2 : ℝ) := by positivity
  have hspos : 0 < Real.sqrt (1 + r ^ 2) :=
    Real.sqrt_pos.2 hqpos
  have hsne : Real.sqrt (1 + r ^ 2) ≠ 0 :=
    ne_of_gt hspos
  have hs2 :
      Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt hqpos.le
  unfold hMinusApply potential
  rw [resonanceMinus_second_deriv_closed]
  unfold resonanceMinusSecondDerivative resonanceMinus
  change
    -(-3 * r * (Real.sqrt (1 + r ^ 2) ^ 5)⁻¹) -
      (3 / (1 + r ^ 2) ^ 2) *
        (r * (Real.sqrt (1 + r ^ 2))⁻¹) = 0
  have hs4 :
      (1 + r ^ 2) ^ 2 =
        Real.sqrt (1 + r ^ 2) ^ 4 := by
    rw [← hs2]
    ring
  rw [hs4]
  field_simp [hsne]
  ring

end HBL.Modulation.AffineTail
