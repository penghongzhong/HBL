import HBL.AffineTailBoundaryData
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Far-field limit in the H-minus affine-tail Green identity.

The phase resonance is
  psi_-(r) = r / sqrt(1+r^2).
For r>0 this equals
  (sqrt(1+r^{-2}))^{-1},
so psi_-(r) -> 1.  The far Green boundary simplifies exactly to
  -psi_-(r)^3,
hence tends to -1.  This is the concrete c_- = 1 instance of the
manuscript boundary computation.
-/

noncomputable section

open Filter
open scoped Topology

namespace HBL.Modulation.AffineTail

/-- Positive-radius normalization of the phase resonance. -/
theorem resonanceMinus_eq_inv_sqrt_one_add_inv_sq
    (r : ℝ) (hr : 0 < r) :
    resonanceMinus r =
      (Real.sqrt (1 + (r⁻¹) ^ 2))⁻¹ := by
  have hr0 : 0 ≤ r := hr.le
  have hrne : r ≠ 0 := ne_of_gt hr
  have hBpos : 0 < (1 + (r⁻¹) ^ 2 : ℝ) := by positivity
  have hsne : Real.sqrt (1 + (r⁻¹) ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hBpos)
  have hfac :
      (1 + r ^ 2 : ℝ) =
        r ^ 2 * (1 + (r⁻¹) ^ 2) := by
    field_simp [hrne]
    ring
  unfold resonanceMinus radialResonanceMinus bubble
  rw [hfac, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr0]
  field_simp [hrne, hsne]

/-- The manuscript phase resonance has asymptotic constant c_- = 1. -/
theorem resonanceMinus_tendsto_one :
    Tendsto resonanceMinus atTop (𝓝 (1 : ℝ)) := by
  have hinv :
      Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hinv2 :
      Tendsto (fun r : ℝ => (r⁻¹) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using hinv.pow 2
  have hadd :
      Tendsto (fun r : ℝ => 1 + (r⁻¹) ^ 2)
        atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add hinv2
  have hsqrt :
      Tendsto (fun r : ℝ => Real.sqrt (1 + (r⁻¹) ^ 2))
        atTop (𝓝 (1 : ℝ)) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hadd
    simpa using h
  have hnormal :
      Tendsto (fun r : ℝ =>
        (Real.sqrt (1 + (r⁻¹) ^ 2))⁻¹)
        atTop (𝓝 (1 : ℝ)) := by
    simpa using hsqrt.inv₀ one_ne_zero
  apply hnormal.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (resonanceMinus_eq_inv_sqrt_one_add_inv_sq r hr).symm

/-- The explicit far boundary collapses to minus the cube of the resonance. -/
theorem greenBoundary_minus_far_eq_neg_cube
    (R : ℝ) (hR : 2 < R) :
    greenBoundary resonanceMinus (deriv resonanceMinus)
      model (deriv model) R =
      -(resonanceMinus R) ^ 3 := by
  rw [greenBoundary_minus_far R hR]
  have hspos : 0 < Real.sqrt (1 + R ^ 2) := by positivity
  have hsne : Real.sqrt (1 + R ^ 2) ≠ 0 := ne_of_gt hspos
  have hs2 :
      Real.sqrt (1 + R ^ 2) ^ 2 = 1 + R ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold resonanceMinus radialResonanceMinus bubble
  unfold bubbleRadialEnergyDerivative
  field_simp [hsne]
  nlinarith [hs2]

/-- The Green boundary has the manuscript limit -c_- = -1. -/
theorem greenBoundary_minus_tendsto_neg_one :
    Tendsto
      (fun R : ℝ =>
        greenBoundary resonanceMinus (deriv resonanceMinus)
          model (deriv model) R)
      atTop (𝓝 (-1 : ℝ)) := by
  have hcub :
      Tendsto (fun R : ℝ => -(resonanceMinus R) ^ 3)
        atTop (𝓝 (-1 : ℝ)) := by
    have h := resonanceMinus_tendsto_one.pow 3
    have hn := h.neg
    simpa using hn
  apply hcub.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with R hR
  exact (greenBoundary_minus_far_eq_neg_cube R hR).symm

end HBL.Modulation.AffineTail
