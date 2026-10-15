import HBL.CompactTestCauchy
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
The radial conjugation `U f = r f(r)` and the quantitative bound behind the
manuscript sentence saying that compact threshold tests are continuous on the
radial energy space.
-/

noncomputable section

open Set MeasureTheory Filter

namespace HBL.Modulation

/-- The manuscript's radial conjugation, with the harmless factor
`sqrt (4*pi)` omitted exactly as in the paper. -/
def radialU (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * f r

theorem radialU_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (radialU f) := by
  simpa [radialU] using continuous_id.mul hf

/-- The compact threshold pairing on a support interval. -/
def compactThresholdPairing (R : ℝ) (zeta f : ℝ → ℝ) : ℝ :=
  ∫ r, zeta r * radialU f r ∂(volume.restrict (Ioc 0 R))

/-- First half of the continuity estimate: absolute value of the threshold
pairing is bounded by the product of the two finite-interval L2 norms. -/
theorem compactThresholdPairing_abs_le
    (R : ℝ) (hR : 0 ≤ R)
    (zeta f : ℝ → ℝ) (hzeta : Continuous zeta) (hf : Continuous f) :
    |compactThresholdPairing R zeta f| ≤
      (∫ r, ‖zeta r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) ^ ((1 : ℝ) / 2) *
      (∫ r, ‖radialU f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) ^ ((1 : ℝ) / 2) := by
  let mu : Measure ℝ := volume.restrict (Ioc 0 R)
  have hnorm :
      ‖∫ r, zeta r * radialU f r ∂mu‖ ≤
        ∫ r, ‖zeta r * radialU f r‖ ∂mu :=
    norm_integral_le_integral_norm _
  have hcs := compactTest_cauchySchwarz R hR zeta (radialU f)
    hzeta (radialU_continuous hf)
  calc
    |compactThresholdPairing R zeta f|
        = ‖∫ r, zeta r * radialU f r ∂mu‖ := by
            simp [compactThresholdPairing, mu, Real.norm_eq_abs]
    _ ≤ ∫ r, ‖zeta r * radialU f r‖ ∂mu := hnorm
    _ = ∫ r, ‖zeta r‖ * ‖radialU f r‖ ∂mu := by
          congr 1
          funext r
          exact norm_mul _ _
    _ ≤ _ := by
          simpa [mu] using hcs

/-- On a compact radial interval, the L2 norm of `U f = r f` is bounded by
`R` times the local L2 norm of `f`. -/
theorem radialU_L2_sq_le_local
    (R : ℝ) (hR : 0 ≤ R) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ r, ‖radialU f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) ≤
      R ^ 2 * (∫ r, ‖f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) := by
  let mu : Measure ℝ := volume.restrict (Ioc 0 R)
  have hU2 :
      MemLp (radialU f) (ENNReal.ofReal (2 : ℝ)) mu := by
    simpa [mu] using
      continuous_memLp_restrict_Ioc 0 R hR (radialU f)
        (radialU_continuous hf) (ENNReal.ofReal (2 : ℝ))
  have hf2 :
      MemLp f (ENNReal.ofReal (2 : ℝ)) mu := by
    simpa [mu] using
      continuous_memLp_restrict_Ioc 0 R hR f hf (ENNReal.ofReal (2 : ℝ))
  have hUint :
      Integrable (fun r => ‖radialU f r‖ ^ (2 : ℝ)) mu := by
    simpa using hU2.integrable_norm_rpow (by norm_num) (by simp)
  have hfint :
      Integrable (fun r => ‖f r‖ ^ (2 : ℝ)) mu := by
    simpa using hf2.integrable_norm_rpow (by norm_num) (by simp)
  have hmono :
      (∫ r, ‖radialU f r‖ ^ (2 : ℝ) ∂mu) ≤
        ∫ r, R ^ 2 * ‖f r‖ ^ (2 : ℝ) ∂mu := by
    apply integral_mono_ae hUint (hfint.const_mul (R ^ 2))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := le_of_lt hr.1
    have hrR : r ≤ R := hr.2
    have hrsq : r ^ 2 ≤ R ^ 2 := by
      nlinarith
    simp only [radialU, norm_mul, Real.rpow_two]
    rw [Real.norm_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_right hrsq (sq_nonneg ‖f r‖)
  calc
    (∫ r, ‖radialU f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R)))
        ≤ ∫ r, R ^ 2 * ‖f r‖ ^ (2 : ℝ) ∂mu := by
            simpa [mu] using hmono
    _ = R ^ 2 * (∫ r, ‖f r‖ ^ (2 : ℝ) ∂mu) := by
          rw [integral_const_mul]
    _ = R ^ 2 *
        (∫ r, ‖f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) := by
          rfl

/-- If the standard radial Hardy estimate is supplied in its local consequence,
then the compact threshold pairing has an explicit homogeneous-energy bound.
This isolates exactly the standard-analysis input used by the manuscript. -/
theorem compactThresholdPairing_abs_le_of_hardy
    (R energy : ℝ) (hR : 0 ≤ R)
    (zeta f : ℝ → ℝ) (hzeta : Continuous zeta) (hf : Continuous f)
    (hHardy :
      (∫ r, ‖f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) ≤ 4 * energy) :
    |compactThresholdPairing R zeta f| ≤
      (∫ r, ‖zeta r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) ^ ((1 : ℝ) / 2) *
      (4 * R ^ 2 * energy) ^ ((1 : ℝ) / 2) := by
  have hPair :=
    compactThresholdPairing_abs_le R hR zeta f hzeta hf
  have hU :=
    radialU_L2_sq_le_local R hR f hf
  have hUHardy :
      (∫ r, ‖radialU f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) ≤
        4 * R ^ 2 * energy := by
    calc
      (∫ r, ‖radialU f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R)))
          ≤ R ^ 2 *
            (∫ r, ‖f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) := hU
      _ ≤ R ^ 2 * (4 * energy) :=
        mul_le_mul_of_nonneg_left hHardy (sq_nonneg R)
      _ = 4 * R ^ 2 * energy := by ring
  have hU_nonneg :
      0 ≤ ∫ r, ‖radialU f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R)) :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have hroot :
      (∫ r, ‖radialU f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) ^ ((1 : ℝ) / 2)
        ≤ (4 * R ^ 2 * energy) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hU_nonneg hUHardy (by norm_num)
  exact hPair.trans
    (mul_le_mul_of_nonneg_left hroot
      (Real.rpow_nonneg
        (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _))

end HBL.Modulation
