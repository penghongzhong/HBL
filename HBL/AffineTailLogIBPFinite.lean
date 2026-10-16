import HBL.AffineTailPVLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Finite-cutoff integration by parts for the affine logarithmic density.

For r>0 and 0<e<r, both intervals [0,r-e] and [r+e,R] avoid the
logarithmic/Cauchy singularity at rho=r.  On each interval we rigorously
integrate
  P'(rho) * (log(r+rho)-log(r-rho))
by parts, where
  P(rho)=rho^2/(4(1+rho^2)^2).
No principal-value passage is made here; all integrals are ordinary finite
interval integrals.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology Interval

namespace HBL.Modulation.AffineTail

/-- The affine logarithmic density equals the primitive derivative times
the split logarithm away from the two real logarithmic poles. -/
theorem affineLogDensity_eq_deriv_mul_splitLog
    (r rho : ℝ) (hp : r + rho ≠ 0) (hm : r - rho ≠ 0) :
    affineLogDensity r rho =
      deriv radialLogPrimitive rho *
        (Real.log (r + rho) - Real.log (r - rho)) := by
  rw [affineLogDensity_primitive_deriv,
    radialLog_ratio_eq_sub r rho hp hm]

/-- Integration by parts on the left side of the singular radius. -/
theorem affineLogDensity_integral_left_ibp
    (r e : ℝ) (hr : 0 < r) (he : 0 < e) (her : e < r) :
    (∫ rho in (0 : ℝ)..(r - e), affineLogDensity r rho) =
      (Real.log (r + (r - e)) - Real.log (r - (r - e))) *
          radialLogPrimitive (r - e) -
        (Real.log (r + 0) - Real.log (r - 0)) *
          radialLogPrimitive 0 -
        (∫ rho in (0 : ℝ)..(r - e),
          (2 * r / (r ^ 2 - rho ^ 2)) *
            radialLogPrimitive rho) := by
  have h0 : (0 : ℝ) ≤ r - e := by linarith
  have hU :
      ∀ rho ∈ Set.uIcc (0 : ℝ) (r - e),
        HasDerivAt
          (fun x : ℝ => Real.log (r + x) - Real.log (r - x))
          (2 * r / (r ^ 2 - rho ^ 2)) rho := by
    intro rho hρ
    rw [Set.uIcc_of_le h0] at hρ
    exact splitRadialLog_hasDerivAt r rho
      (ne_of_gt (by linarith [hρ.1, hρ.2]))
      (ne_of_gt (by linarith [hρ.2]))
  have hV :
      ∀ rho ∈ Set.uIcc (0 : ℝ) (r - e),
        HasDerivAt radialLogPrimitive
          (rho * (1 - rho ^ 2) /
            (2 * (1 + rho ^ 2) ^ 3)) rho := by
    intro rho _
    exact radialLogPrimitive_hasDerivAt rho
  have hden :
      ∀ rho ∈ Set.uIcc (0 : ℝ) (r - e),
        r ^ 2 - rho ^ 2 ≠ 0 := by
    intro rho hρ
    rw [Set.uIcc_of_le h0] at hρ
    have hp : 0 < r + rho := by linarith [hρ.1]
    have hm : 0 < r - rho := by linarith [hρ.2]
    nlinarith [mul_pos hp hm]
  have hUcont :
      ContinuousOn
        (fun rho : ℝ => 2 * r / (r ^ 2 - rho ^ 2))
        (Set.uIcc (0 : ℝ) (r - e)) := by
    apply ContinuousOn.div continuousOn_const
      (continuous_const.sub (continuous_id.pow 2)).continuousOn
    exact hden
  have hVcont :
      Continuous
        (fun rho : ℝ =>
          rho * (1 - rho ^ 2) /
            (2 * (1 + rho ^ 2) ^ 3)) := by
    fun_prop (discharger := intro; positivity)
  have hIBP :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := r - e)
      (u := fun x : ℝ => Real.log (r + x) - Real.log (r - x))
      (u' := fun x : ℝ => 2 * r / (r ^ 2 - x ^ 2))
      (v := radialLogPrimitive)
      (v' := fun x : ℝ =>
        x * (1 - x ^ 2) / (2 * (1 + x ^ 2) ^ 3))
      hU hV
      (hUcont.intervalIntegrable (μ := volume))
      (hVcont.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := r - e))
  calc
    (∫ rho in (0 : ℝ)..(r - e), affineLogDensity r rho) =
        ∫ rho in (0 : ℝ)..(r - e),
          (Real.log (r + rho) - Real.log (r - rho)) *
            (rho * (1 - rho ^ 2) /
              (2 * (1 + rho ^ 2) ^ 3)) := by
      apply intervalIntegral.integral_congr
      intro rho hρ
      rw [Set.uIcc_of_le h0] at hρ
      rw [affineLogDensity_eq_deriv_mul_splitLog r rho
        (ne_of_gt (by linarith [hρ.1, hρ.2]))
        (ne_of_gt (by linarith [hρ.2])),
        (radialLogPrimitive_hasDerivAt rho).deriv]
      ring
    _ = _ := hIBP

/-- Integration by parts on the right side of the singular radius. -/
theorem affineLogDensity_integral_right_ibp
    (r e R : ℝ) (hr : 0 < r) (he : 0 < e)
    (hR : r + e ≤ R) :
    (∫ rho in (r + e)..R, affineLogDensity r rho) =
      (Real.log (r + R) - Real.log (r - R)) *
          radialLogPrimitive R -
        (Real.log (r + (r + e)) - Real.log (r - (r + e))) *
          radialLogPrimitive (r + e) -
        (∫ rho in (r + e)..R,
          (2 * r / (r ^ 2 - rho ^ 2)) *
            radialLogPrimitive rho) := by
  have hU :
      ∀ rho ∈ Set.uIcc (r + e) R,
        HasDerivAt
          (fun x : ℝ => Real.log (r + x) - Real.log (r - x))
          (2 * r / (r ^ 2 - rho ^ 2)) rho := by
    intro rho hρ
    rw [Set.uIcc_of_le hR] at hρ
    exact splitRadialLog_hasDerivAt r rho
      (ne_of_gt (by linarith [hρ.1]))
      (ne_of_lt (by linarith [hρ.1]))
  have hV :
      ∀ rho ∈ Set.uIcc (r + e) R,
        HasDerivAt radialLogPrimitive
          (rho * (1 - rho ^ 2) /
            (2 * (1 + rho ^ 2) ^ 3)) rho := by
    intro rho _
    exact radialLogPrimitive_hasDerivAt rho
  have hden :
      ∀ rho ∈ Set.uIcc (r + e) R,
        r ^ 2 - rho ^ 2 ≠ 0 := by
    intro rho hρ
    rw [Set.uIcc_of_le hR] at hρ
    have hp : 0 < r + rho := by linarith [hρ.1]
    have hm : r - rho < 0 := by linarith [hρ.1]
    nlinarith [mul_neg_of_pos_of_neg hp hm]
  have hUcont :
      ContinuousOn
        (fun rho : ℝ => 2 * r / (r ^ 2 - rho ^ 2))
        (Set.uIcc (r + e) R) := by
    apply ContinuousOn.div continuousOn_const
      (continuous_const.sub (continuous_id.pow 2)).continuousOn
    exact hden
  have hVcont :
      Continuous
        (fun rho : ℝ =>
          rho * (1 - rho ^ 2) /
            (2 * (1 + rho ^ 2) ^ 3)) := by
    fun_prop (discharger := intro; positivity)
  have hIBP :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := r + e) (b := R)
      (u := fun x : ℝ => Real.log (r + x) - Real.log (r - x))
      (u' := fun x : ℝ => 2 * r / (r ^ 2 - x ^ 2))
      (v := radialLogPrimitive)
      (v' := fun x : ℝ =>
        x * (1 - x ^ 2) / (2 * (1 + x ^ 2) ^ 3))
      hU hV
      (hUcont.intervalIntegrable (μ := volume))
      (hVcont.intervalIntegrable (μ := volume) (a := r + e) (b := R))
  calc
    (∫ rho in (r + e)..R, affineLogDensity r rho) =
        ∫ rho in (r + e)..R,
          (Real.log (r + rho) - Real.log (r - rho)) *
            (rho * (1 - rho ^ 2) /
              (2 * (1 + rho ^ 2) ^ 3)) := by
      apply intervalIntegral.integral_congr
      intro rho hρ
      rw [Set.uIcc_of_le hR] at hρ
      rw [affineLogDensity_eq_deriv_mul_splitLog r rho
        (ne_of_gt (by linarith [hρ.1]))
        (ne_of_lt (by linarith [hρ.1])),
        (radialLogPrimitive_hasDerivAt rho).deriv]
      ring
    _ = _ := hIBP

/-- Exact sum of the two finite integration-by-parts formulas. -/
theorem affineLogDensity_integral_split_ibp
    (r e R : ℝ) (hr : 0 < r) (he : 0 < e)
    (her : e < r) (hR : r + e ≤ R) :
    (∫ rho in (0 : ℝ)..(r - e), affineLogDensity r rho) +
        (∫ rho in (r + e)..R, affineLogDensity r rho) =
      ((Real.log (r + (r - e)) - Real.log (r - (r - e))) *
          radialLogPrimitive (r - e) -
        (Real.log (r + 0) - Real.log (r - 0)) *
          radialLogPrimitive 0) +
      ((Real.log (r + R) - Real.log (r - R)) *
          radialLogPrimitive R -
        (Real.log (r + (r + e)) - Real.log (r - (r + e))) *
          radialLogPrimitive (r + e)) -
      ((∫ rho in (0 : ℝ)..(r - e),
          (2 * r / (r ^ 2 - rho ^ 2)) *
            radialLogPrimitive rho) +
        (∫ rho in (r + e)..R,
          (2 * r / (r ^ 2 - rho ^ 2)) *
            radialLogPrimitive rho)) := by
  rw [affineLogDensity_integral_left_ibp r e hr he her,
    affineLogDensity_integral_right_ibp r e R hr he hR]
  ring

end HBL.Modulation.AffineTail
