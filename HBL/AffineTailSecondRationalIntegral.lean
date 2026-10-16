import HBL.AffineTailRationalIntegrability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
Exact value of the squared-denominator rational integral appearing in
the principal-value reduction of the affine Hartree logarithmic kernel.

The proof uses an explicit primitive, the genuine L1 integrability
theorem from AffineTailRationalIntegrability, and the improper FTC.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace HBL.Modulation.AffineTail

/-- Exact primitive for (1+x^2)^(-2). -/
def secondRationalPrimitive (x : ℝ) : ℝ :=
  (Real.arctan x + x / (1 + x ^ 2)) / 2

theorem secondRationalPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt secondRationalPrimitive
      (((1 + x ^ 2) ^ 2)⁻¹) x := by
  have hq : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)
    convert h using 1
    · funext y
      simp
    · norm_num
  have hqne : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
  have hh := ((Real.hasDerivAt_arctan' x).add
    ((hasDerivAt_id x).div hq hqne)).div_const 2
  convert hh using 1 <;>
    simp only [secondRationalPrimitive, Pi.add_apply, Pi.div_apply,
      id_eq, one_mul, zero_add] <;>
    (first | rfl | (field_simp [hqne] <;> ring))

theorem rational_over_one_add_sq_tendsto_zero :
    Tendsto (fun x : ℝ => x / (1 + x ^ 2))
      atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹)
      atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have hinv2 : Tendsto (fun x : ℝ => (x⁻¹) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by simpa using hinv.pow 2
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have hden : Tendsto (fun x : ℝ => 1 + (x⁻¹) ^ 2)
      atTop (𝓝 (1 : ℝ)) := by simpa using hone.add hinv2
  have hratio :
      Tendsto (fun x : ℝ => x⁻¹ / (1 + (x⁻¹) ^ 2))
        atTop (𝓝 (0 : ℝ)) := by
    have h := hinv.div hden (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  apply hratio.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hne : x ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) hx)
  have hA : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
  have hB : (1 + (x⁻¹) ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hne, hA, hB]
  ring

theorem secondRationalPrimitive_tendsto_pi_div_four :
    Tendsto secondRationalPrimitive atTop (𝓝 (Real.pi / 4)) := by
  have ha : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have h := (ha.add rational_over_one_add_sq_tendsto_zero).div_const 2
  unfold secondRationalPrimitive
  convert h using 1 <;> ring

/-- The second elementary integral in the Hartree affine charge is pi/4. -/
theorem second_rational_integral :
    (∫ x in Ioi (0 : ℝ), ((1 + x ^ 2) ^ 2)⁻¹) = Real.pi / 4 := by
  have h :
      (∫ x in Ioi (0 : ℝ), ((1 + x ^ 2) ^ 2)⁻¹) =
        Real.pi / 4 - secondRationalPrimitive 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x _ => secondRationalPrimitive_hasDerivAt x)
      second_rational_integrableOn
      secondRationalPrimitive_tendsto_pi_div_four
  simpa [secondRationalPrimitive] using h

end HBL.Modulation.AffineTail
