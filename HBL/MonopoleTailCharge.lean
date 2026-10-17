import HBL.AffineTailSecondRationalIntegral
import HBL.AffineTailLemmaClosed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
Exact threshold pairing for the first slow monopole source.  This is the
numerical input in the manuscript identity

  ell_mon = -(1 / c_+) * integral psi_+(r) r W(r)^3 dr = -pi/8.

All integrals below are genuine Lebesgue integrals on the positive half-line.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace HBL.Modulation.AffineTail

/-- A primitive of `(1+x^2)^(-3)`. -/
def thirdRationalPrimitive (x : ℝ) : ℝ :=
  (3 * Real.arctan x + 3 * x / (1 + x ^ 2) +
    2 * x / (1 + x ^ 2) ^ 2) / 8

theorem thirdRationalPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt thirdRationalPrimitive (((1 + x ^ 2) ^ 3)⁻¹) x := by
  have hq : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1
    · funext y
      simp
    · norm_num
  have hqne : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
  have hq2 : HasDerivAt (fun y : ℝ => (1 + y ^ 2) ^ 2)
      (2 * (1 + x ^ 2) * (2 * x)) x := by
    convert hq.pow 2 using 1
    · norm_num
  have hq2ne : (1 + x ^ 2 : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hqne
  have h :=
    (((Real.hasDerivAt_arctan' x).const_mul 3).add
      ((hasDerivAt_id x).const_mul 3 |>.div hq hqne)).add
      ((hasDerivAt_id x).const_mul 2 |>.div hq2 hq2ne) |>.div_const 8
  convert h using 1
  · funext y
    simp only [thirdRationalPrimitive, Pi.add_apply, Pi.div_apply, id_eq]
  ·
    simp only [id_eq]
    field_simp [hqne]
    ring

theorem inv_cube_rational_norm_le (x : ℝ) :
    ‖((1 + x ^ 2) ^ 3)⁻¹‖ ≤ ‖((1 + x ^ 2) ^ 2)⁻¹‖ := by
  have hp : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hle : (1 + x ^ 2 : ℝ) ^ 2 ≤ (1 + x ^ 2) ^ 3 := by
    have hbase : 1 ≤ (1 + x ^ 2 : ℝ) := by nlinarith [sq_nonneg x]
    nlinarith [sq_nonneg (1 + x ^ 2)]
  have hInv := one_div_le_one_div_of_le (pow_pos hp 2) hle
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (pow_pos hp 3)),
    abs_of_pos (inv_pos.mpr (pow_pos hp 2))]
  simpa only [one_div] using hInv

theorem third_rational_integrable :
    Integrable (fun x : ℝ => ((1 + x ^ 2) ^ 3)⁻¹) := by
  have hc : Continuous (fun x : ℝ => 1 + x ^ 2) := by fun_prop
  have hne (x : ℝ) : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
  have hm : AEStronglyMeasurable (fun x : ℝ => ((1 + x ^ 2) ^ 3)⁻¹) :=
    ((hc.pow 3).inv₀ (fun x => pow_ne_zero 3 (hne x))).aestronglyMeasurable
  exact second_rational_integrable.mono' hm
    (ae_of_all _ fun x => by
      have hp : (0 : ℝ) < 1 + x ^ 2 := by positivity
      simpa only [Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (pow_pos hp 2))] using
        inv_cube_rational_norm_le x)

theorem third_rational_integrableOn :
    IntegrableOn (fun x : ℝ => ((1 + x ^ 2) ^ 3)⁻¹) (Ioi 0) :=
  third_rational_integrable.integrableOn

theorem inv_one_add_sq_tendsto_zero :
    Tendsto (fun x : ℝ => (1 + x ^ 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hinv2 : Tendsto (fun x : ℝ => (x⁻¹) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by simpa using hinv.pow 2
  have hden : Tendsto (fun x : ℝ => 1 + (x⁻¹) ^ 2)
      atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.add hinv2)
  have hratio : Tendsto
      (fun x : ℝ => (x⁻¹) ^ 2 / (1 + (x⁻¹) ^ 2))
      atTop (𝓝 (0 : ℝ)) := by
    convert hinv2.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
    · simp only [zero_div]
  apply hratio.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hxne : x ≠ 0 := by linarith
  field_simp [hxne]
  ring

theorem rational_over_one_add_sq_sq_tendsto_zero :
    Tendsto (fun x : ℝ => x / (1 + x ^ 2) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  have h := rational_over_one_add_sq_tendsto_zero.mul
    inv_one_add_sq_tendsto_zero
  convert h using 1
  · funext x
    field_simp [show (1 + x ^ 2 : ℝ) ≠ 0 by positivity]
  · simp

theorem thirdRationalPrimitive_tendsto_three_pi_div_sixteen :
    Tendsto thirdRationalPrimitive atTop (𝓝 (3 * Real.pi / 16)) := by
  have ha : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have h := (((ha.const_mul 3).add
      (rational_over_one_add_sq_tendsto_zero.const_mul 3)).add
      (rational_over_one_add_sq_sq_tendsto_zero.const_mul 2)).div_const 8
  unfold thirdRationalPrimitive
  convert h using 1 <;> ring

theorem third_rational_integral :
    (∫ x in Ioi (0 : ℝ), ((1 + x ^ 2) ^ 3)⁻¹) =
      3 * Real.pi / 16 := by
  have h :
      (∫ x in Ioi (0 : ℝ), ((1 + x ^ 2) ^ 3)⁻¹) =
        3 * Real.pi / 16 - thirdRationalPrimitive 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x _ => thirdRationalPrimitive_hasDerivAt x)
      third_rational_integrableOn
      thirdRationalPrimitive_tendsto_three_pi_div_sixteen
  simpa [thirdRationalPrimitive] using h

/-- The rational representative of `psi_+ r W^3`. -/
def monopolePairingDensity (r : ℝ) : ℝ :=
  r ^ 2 * (1 - r ^ 2) / (2 * (1 + r ^ 2) ^ 3)

theorem resonancePlus_mul_monopoleSource (r : ℝ) :
    resonancePlus r * (r * bubble r ^ 3) = monopolePairingDensity r := by
  rw [resonancePlus_def, dilationGenerator_bubble_closed]
  unfold bubble monopolePairingDensity
  have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hs6 : Real.sqrt (1 + r ^ 2) ^ 6 = (1 + r ^ 2) ^ 3 := by
    calc
      Real.sqrt (1 + r ^ 2) ^ 6 =
          (Real.sqrt (1 + r ^ 2) ^ 2) ^ 3 := by ring
      _ = (1 + r ^ 2) ^ 3 := by rw [hs2]
  have hsne : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  field_simp [hsne]
  rw [hs6]

theorem monopolePairingDensity_decomposition (r : ℝ) :
    monopolePairingDensity r =
      -(1 / 2 : ℝ) * (1 + r ^ 2)⁻¹ +
      (3 / 2 : ℝ) * ((1 + r ^ 2) ^ 2)⁻¹ -
      ((1 + r ^ 2) ^ 3)⁻¹ := by
  unfold monopolePairingDensity
  field_simp [show (1 + r ^ 2 : ℝ) ≠ 0 by positivity]
  ring

theorem monopolePairingDensity_integrableOn :
    IntegrableOn monopolePairingDensity (Ioi 0) := by
  rw [show monopolePairingDensity = fun r : ℝ =>
      -(1 / 2 : ℝ) * (1 + r ^ 2)⁻¹ +
      (3 / 2 : ℝ) * ((1 + r ^ 2) ^ 2)⁻¹ -
      ((1 + r ^ 2) ^ 3)⁻¹ by
    funext r
    exact monopolePairingDensity_decomposition r]
  exact (((integrable_inv_one_add_sq.const_mul (-(1 / 2 : ℝ))).add
    (second_rational_integrable.const_mul (3 / 2 : ℝ))).sub
    third_rational_integrable).integrableOn

/-- Exact source pairing in the first monopole correction. -/
theorem monopole_source_pairing_eq_neg_pi_div_sixteen :
    (∫ r in Ioi (0 : ℝ), resonancePlus r * (r * bubble r ^ 3)) =
      -(Real.pi / 16) := by
  rw [show (fun r : ℝ => resonancePlus r * (r * bubble r ^ 3)) =
      monopolePairingDensity by
    funext r
    exact resonancePlus_mul_monopoleSource r]
  rw [show monopolePairingDensity = fun r : ℝ =>
      -(1 / 2 : ℝ) * (1 + r ^ 2)⁻¹ +
      (3 / 2 : ℝ) * ((1 + r ^ 2) ^ 2)⁻¹ -
      ((1 + r ^ 2) ^ 3)⁻¹ by
    funext r
    exact monopolePairingDensity_decomposition r]
  have h1 : IntegrableOn (fun r : ℝ =>
      -(1 / 2 : ℝ) * (1 + r ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul (-(1 / 2 : ℝ))).integrableOn
  have h2 : IntegrableOn (fun r : ℝ =>
      (3 / 2 : ℝ) * ((1 + r ^ 2) ^ 2)⁻¹) (Ioi 0) :=
    (second_rational_integrable.const_mul (3 / 2 : ℝ)).integrableOn
  have h3 : IntegrableOn (fun r : ℝ =>
      ((1 + r ^ 2) ^ 3)⁻¹) (Ioi 0) :=
    third_rational_integrable.integrableOn
  calc
    (∫ r in Ioi (0 : ℝ),
        -(1 / 2 : ℝ) * (1 + r ^ 2)⁻¹ +
          (3 / 2 : ℝ) * ((1 + r ^ 2) ^ 2)⁻¹ -
          ((1 + r ^ 2) ^ 3)⁻¹) =
        (∫ r in Ioi (0 : ℝ), -(1 / 2 : ℝ) * (1 + r ^ 2)⁻¹) +
        (∫ r in Ioi (0 : ℝ), (3 / 2 : ℝ) * ((1 + r ^ 2) ^ 2)⁻¹) -
        (∫ r in Ioi (0 : ℝ), ((1 + r ^ 2) ^ 3)⁻¹) := by
          have hsub := integral_sub (μ := volume.restrict (Ioi (0 : ℝ)))
            (h1.add h2) h3
          have hadd := integral_add (μ := volume.restrict (Ioi (0 : ℝ)))
            h1 h2
          have htail := congrArg
            (fun z : ℝ => z -
              ∫ r in Ioi (0 : ℝ), ((1 + r ^ 2) ^ 3)⁻¹) hadd
          simpa only [Pi.add_apply, Pi.sub_apply] using hsub.trans htail
    _ = -(1 / 2 : ℝ) * (Real.pi / 2) +
        (3 / 2 : ℝ) * (Real.pi / 4) - 3 * Real.pi / 16 := by
          rw [integral_const_mul, integral_const_mul,
            first_rational_integral, second_rational_integral,
            third_rational_integral]
    _ = -(Real.pi / 16) := by ring

/-- The affine slope selected by the real-channel threshold charge. -/
def monopoleAffineSlope : ℝ :=
  -(∫ r in Ioi (0 : ℝ), resonancePlus r * (r * bubble r ^ 3)) /
    channelLimit .plus

theorem monopoleAffineSlope_eq_neg_pi_div_eight :
    monopoleAffineSlope = -(Real.pi / 8) := by
  rw [monopoleAffineSlope, monopole_source_pairing_eq_neg_pi_div_sixteen]
  norm_num [channelLimit]
  ring

end HBL.Modulation.AffineTail
