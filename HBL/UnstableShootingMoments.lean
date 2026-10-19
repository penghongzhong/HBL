import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact absolutely convergent moments of the translated exponential
majorant used by the actual nonautonomous terminal shooting kernel.
The integrals are established by monotone primitives and the improper FTC;
no convergence or integral identity is assumed. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Shooting

private theorem shiftedExp_hasDerivAt (e s t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-e * (x - s)))
      (-e * Real.exp (-e * (t - s))) t := by
  simpa only [mul_one, id_eq, mul_comm] using
    (((hasDerivAt_id t).sub_const s).const_mul (-e)).exp

private theorem shiftedExp_tendsto_zero {e : ℝ} (he : 0 < e) (s : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (-e * (t - s))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-e * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 e he
  have hshift : Tendsto (fun t : ℝ => t - s) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      (tendsto_atTop_add_const_right atTop (-s) (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))
  exact h0.comp hshift

private theorem shiftedExp_firstMoment_tendsto_zero {e : ℝ} (he : 0 < e) (s : ℝ) :
    Tendsto (fun t : ℝ => (t - s) * Real.exp (-e * (t - s))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t * Real.exp (-e * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 e he
  have hshift : Tendsto (fun t : ℝ => t - s) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      (tendsto_atTop_add_const_right atTop (-s) (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))
  exact h1.comp hshift

private theorem shiftedExp_primitive_hasDerivAt {e : ℝ} (he : 0 < e) (s t : ℝ) :
    HasDerivAt (fun x : ℝ => -Real.exp (-e * (x - s)) / e)
      (Real.exp (-e * (t - s))) t := by
  convert ((shiftedExp_hasDerivAt e s t).neg).div_const e using 1
  field_simp [he.ne']

/-- Absolute convergence of the translated exponential majorant for every
real lower endpoint and every strictly positive decay rate. -/
theorem shootingExp_integrable {e : ℝ} (he : 0 < e) (s : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-e * (t - s))) (Ioi s) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => shiftedExp_primitive_hasDerivAt he s t)
    (fun t _ => (Real.exp_pos _).le)
  simpa only [neg_zero, zero_div] using (shiftedExp_tendsto_zero he s).neg.div_const e

/-- The sharp zeroth-moment constant is exactly `1 / e`. -/
theorem shootingExp_integral {e : ℝ} (he : 0 < e) (s : ℝ) :
    (∫ t in Ioi s, Real.exp (-e * (t - s))) = 1 / e := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => shiftedExp_primitive_hasDerivAt he s t)
    (shootingExp_integrable he s)
    (by simpa only [neg_zero, zero_div] using
      (shiftedExp_tendsto_zero he s).neg.div_const e)
  simpa only [sub_self, mul_zero, Real.exp_zero, zero_sub, neg_div, neg_neg] using h

private theorem shiftedExp_firstPrimitive_hasDerivAt {e : ℝ} (he : 0 < e) (s t : ℝ) :
    HasDerivAt
      (fun x : ℝ => -((x - s) / e + 1 / e ^ 2) * Real.exp (-e * (x - s)))
      ((t - s) * Real.exp (-e * (t - s))) t := by
  have hlin := (((hasDerivAt_id t).sub_const s).div_const e).add_const (1 / e ^ 2)
  convert (hlin.mul (shiftedExp_hasDerivAt e s t)).neg using 1
  · funext x
    simp only [Pi.neg_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [id_eq]
    field_simp [he.ne']
    ring

private theorem shiftedExp_firstPrimitive_tendsto_zero {e : ℝ} (he : 0 < e) (s : ℝ) :
    Tendsto
      (fun t : ℝ => -((t - s) / e + 1 / e ^ 2) * Real.exp (-e * (t - s)))
      atTop (𝓝 0) := by
  have h := (((shiftedExp_firstMoment_tendsto_zero he s).div_const e).add
    ((shiftedExp_tendsto_zero he s).div_const (e ^ 2))).neg
  convert h using 1
  · funext t
    ring
  · simp

/-- Absolute convergence of the first moment, needed for the coefficient
variation of a genuinely defined exponential kernel. -/
theorem shootingFirstMoment_integrable {e : ℝ} (he : 0 < e) (s : ℝ) :
    IntegrableOn (fun t : ℝ => (t - s) * Real.exp (-e * (t - s))) (Ioi s) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => shiftedExp_firstPrimitive_hasDerivAt he s t)
    (fun t ht => mul_nonneg (sub_nonneg.mpr ht.le) (Real.exp_pos _).le)
  exact shiftedExp_firstPrimitive_tendsto_zero he s

/-- The sharp first-moment constant is exactly `1 / e^2`. -/
theorem shootingFirstMoment_integral {e : ℝ} (he : 0 < e) (s : ℝ) :
    (∫ t in Ioi s, (t - s) * Real.exp (-e * (t - s))) = 1 / e ^ 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => shiftedExp_firstPrimitive_hasDerivAt he s t)
    (shootingFirstMoment_integrable he s)
    (shiftedExp_firstPrimitive_tendsto_zero he s)
  simpa using h

end HBL.Shooting
