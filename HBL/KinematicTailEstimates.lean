import HBL.KinematicSliceDefinitions

/-!
Direct estimates for the actual reciprocal-tail synchronization equation.
The parameter dependence is proved from the exact affine dependence of
`sliceClock` on the parameter; no derivative of the tail is assumed.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Kinematic

theorem sliceIntegrand_eq_neg_shift_mul_inv
    {A s₀ κ s : ℝ} {h : ℝ → ℝ}
    (hq : sliceClock A s₀ κ h s ≠ 0) (hAs : A * s ≠ 0) :
    sliceIntegrand A s₀ κ h s =
      -(κ + clockPerturbation s₀ h s) *
        ((sliceClock A s₀ κ h s)⁻¹ * (A * s)⁻¹) := by
  unfold sliceIntegrand
  have hA := (mul_ne_zero_iff.mp hAs).1
  have hs := (mul_ne_zero_iff.mp hAs).2
  field_simp [hq, hA, hs]
  simp only [sliceClock]
  ring

theorem sliceIntegrand_abs_le
    {A s₀ κ s δ B c : ℝ} {h : ℝ → ℝ}
    (hA : 0 < A) (hs : 0 < s) (hc : 0 < c)
    (hq : c * s ≤ sliceClock A s₀ κ h s)
    (hp : |clockPerturbation s₀ h s| ≤ B * s ^ (1 - δ)) :
    |sliceIntegrand A s₀ κ h s| ≤
      (|κ| / (c * A)) * s ^ (-2 : ℝ) +
        (B / (c * A)) * s ^ (-1 - δ) := by
  have hqpos : 0 < sliceClock A s₀ κ h s := (mul_pos hc hs).trans_le hq
  have hAs : 0 < A * s := mul_pos hA hs
  have hnum : |κ + clockPerturbation s₀ h s| ≤ |κ| + B * s ^ (1 - δ) :=
    (abs_add_le _ _).trans (add_le_add le_rfl hp)
  have hinv : (sliceClock A s₀ κ h s)⁻¹ ≤ (c * s)⁻¹ :=
    inv_anti₀ (mul_pos hc hs) hq
  have hmul : ((c * s)⁻¹ * (A * s)⁻¹) =
      (c * A)⁻¹ * s ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (le_of_lt hs), Real.rpow_two]
    simp only [mul_inv, pow_two]
    ring
  have hpow : s ^ (1 - δ) * s ^ (-2 : ℝ) = s ^ (-1 - δ) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  rw [sliceIntegrand_eq_neg_shift_mul_inv hqpos.ne' hAs.ne',
    abs_mul, abs_neg, abs_mul, abs_inv, abs_inv,
    abs_of_pos hqpos, abs_of_pos hAs]
  calc
    |κ + clockPerturbation s₀ h s| *
        ((sliceClock A s₀ κ h s)⁻¹ * (A * s)⁻¹) ≤
      (|κ| + B * s ^ (1 - δ)) * ((c * s)⁻¹ * (A * s)⁻¹) :=
      mul_le_mul hnum (mul_le_mul_of_nonneg_right hinv (inv_nonneg.mpr hAs.le))
        (mul_nonneg (inv_nonneg.mpr hqpos.le) (inv_nonneg.mpr hAs.le))
        ((abs_nonneg _).trans hnum)
    _ = (|κ| / (c * A)) * s ^ (-2 : ℝ) +
        (B / (c * A)) * s ^ (-1 - δ) := by
      rw [hmul, add_mul]
      simp only [div_eq_mul_inv]
      calc
        |κ| * ((c * A)⁻¹ * s ^ (-2 : ℝ)) +
            B * s ^ (1 - δ) * ((c * A)⁻¹ * s ^ (-2 : ℝ)) =
          |κ| * (c * A)⁻¹ * s ^ (-2 : ℝ) +
            B * (c * A)⁻¹ * (s ^ (1 - δ) * s ^ (-2 : ℝ)) := by ring
        _ = _ := by rw [hpow]

theorem sliceIntegrand_integrableOn
    {A s₀ κ δ B c : ℝ} {h : ℝ → ℝ}
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hc : 0 < c)
    (hcont : ContinuousOn (sliceClock A s₀ κ h) (Ioi s₀))
    (hq : ∀ s ∈ Ioi s₀, c * s ≤ sliceClock A s₀ κ h s)
    (hp : ∀ s ∈ Ioi s₀, |clockPerturbation s₀ h s| ≤ B * s ^ (1 - δ)) :
    IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀) := by
  have hqpos (s : ℝ) (hs : s ∈ Ioi s₀) : 0 < sliceClock A s₀ κ h s :=
    (mul_pos hc (hs₀.trans hs)).trans_le (hq s hs)
  have hmeas : AEStronglyMeasurable (sliceIntegrand A s₀ κ h)
      (volume.restrict (Ioi s₀)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (hcont.inv₀ (fun s hs => (hqpos s hs).ne')).sub
      ((continuousOn_const.mul continuousOn_id).inv₀
        (fun s hs => (mul_pos hA (hs₀.trans hs)).ne'))
  have hint := ((integrableOn_Ioi_rpow_of_lt
    (by norm_num : (-2 : ℝ) < -1) hs₀).const_mul (|κ| / (c * A))).add
      ((integrableOn_Ioi_rpow_of_lt (show -1 - δ < -1 by linarith) hs₀).const_mul
        (B / (c * A)))
  apply hint.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact sliceIntegrand_abs_le hA (hs₀.trans hs) hc (hq s hs) (hp s hs)

theorem integral_Ioi_rpow_neg_two {s₀ : ℝ} (hs₀ : 0 < s₀) :
    (∫ s : ℝ in Ioi s₀, s ^ (-2 : ℝ)) = s₀⁻¹ := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hs₀]
  norm_num
  rw [Real.rpow_neg_one]

theorem integral_Ioi_rpow_neg_one_sub {s₀ δ : ℝ}
    (hs₀ : 0 < s₀) (hδ : 0 < δ) :
    (∫ s : ℝ in Ioi s₀, s ^ (-1 - δ)) = s₀ ^ (-δ) / δ := by
  rw [integral_Ioi_rpow_of_lt (show -1 - δ < -1 by linarith) hs₀]
  ring_nf

theorem sliceTail_abs_le
    {A s₀ κ δ B c : ℝ} {h : ℝ → ℝ}
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hc : 0 < c)
    (hcont : ContinuousOn (sliceClock A s₀ κ h) (Ioi s₀))
    (hq : ∀ s ∈ Ioi s₀, c * s ≤ sliceClock A s₀ κ h s)
    (hp : ∀ s ∈ Ioi s₀, |clockPerturbation s₀ h s| ≤ B * s ^ (1 - δ)) :
    |sliceTail A s₀ κ h| ≤
      |κ| / (c * A) * s₀⁻¹ + B / (c * A) * (s₀ ^ (-δ) / δ) := by
  have hint := sliceIntegrand_integrableOn hA hs₀ hδ hc hcont hq hp
  have hi₂ := (integrableOn_Ioi_rpow_of_lt
    (by norm_num : (-2 : ℝ) < -1) hs₀).const_mul (|κ| / (c * A))
  have hiδ := (integrableOn_Ioi_rpow_of_lt
    (show -1 - δ < -1 by linarith) hs₀).const_mul (B / (c * A))
  calc
    |sliceTail A s₀ κ h| ≤ ∫ s in Ioi s₀, |sliceIntegrand A s₀ κ h s| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s in Ioi s₀,
        (|κ| / (c * A)) * s ^ (-2 : ℝ) +
          (B / (c * A)) * s ^ (-1 - δ) := by
      apply integral_mono_ae hint.abs (hi₂.add hiδ)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact sliceIntegrand_abs_le hA (hs₀.trans hs) hc (hq s hs) (hp s hs)
    _ = _ := by
      rw [integral_add hi₂ hiδ, integral_const_mul, integral_const_mul,
        integral_Ioi_rpow_neg_two hs₀, integral_Ioi_rpow_neg_one_sub hs₀ hδ]

/-- The positive kernel of the exact parameter difference quotient. -/
def sliceParameterKernel (A s₀ κ η : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  (sliceClock A s₀ κ h s * sliceClock A s₀ η h s)⁻¹

theorem sliceParameterKernel_bounds
    {A s₀ κ η s c d : ℝ} {h : ℝ → ℝ}
    (hs : 0 < s) (hc : 0 < c) (hd : 0 < d)
    (hκ : c * s ≤ sliceClock A s₀ κ h s ∧ sliceClock A s₀ κ h s ≤ d * s)
    (hη : c * s ≤ sliceClock A s₀ η h s ∧ sliceClock A s₀ η h s ≤ d * s) :
    d⁻¹ ^ 2 * s ^ (-2 : ℝ) ≤ sliceParameterKernel A s₀ κ η h s ∧
      sliceParameterKernel A s₀ κ η h s ≤ c⁻¹ ^ 2 * s ^ (-2 : ℝ) := by
  have hpκ := (mul_pos hc hs).trans_le hκ.1
  have hpη := (mul_pos hc hs).trans_le hη.1
  have hlow : (c * s) ^ 2 ≤ sliceClock A s₀ κ h s * sliceClock A s₀ η h s := by
    rw [pow_two]
    exact mul_le_mul hκ.1 hη.1 (mul_pos hc hs).le hpκ.le
  have hupp : sliceClock A s₀ κ h s * sliceClock A s₀ η h s ≤ (d * s) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hκ.2 hη.2 hpη.le (mul_pos hd hs).le
  have hid (x : ℝ) : ((x * s) ^ 2)⁻¹ = x⁻¹ ^ 2 * s ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hs.le, Real.rpow_two]
    simp [mul_pow, inv_pow, mul_comm]
  constructor
  · rw [← hid d]
    exact inv_anti₀ (mul_pos hpκ hpη) hupp
  · rw [← hid c]
    exact inv_anti₀ (sq_pos_of_pos (mul_pos hc hs)) hlow

theorem sliceParameterKernel_integrableOn
    {A s₀ κ η c : ℝ} {h : ℝ → ℝ}
    (hs₀ : 0 < s₀) (hc : 0 < c)
    (hκcont : ContinuousOn (sliceClock A s₀ κ h) (Ioi s₀))
    (hηcont : ContinuousOn (sliceClock A s₀ η h) (Ioi s₀))
    (hκ : ∀ s ∈ Ioi s₀, c * s ≤ sliceClock A s₀ κ h s)
    (hη : ∀ s ∈ Ioi s₀, c * s ≤ sliceClock A s₀ η h s) :
    IntegrableOn (sliceParameterKernel A s₀ κ η h) (Ioi s₀) := by
  have hpκ (s : ℝ) (hs : s ∈ Ioi s₀) : 0 < sliceClock A s₀ κ h s :=
    (mul_pos hc (hs₀.trans hs)).trans_le (hκ s hs)
  have hpη (s : ℝ) (hs : s ∈ Ioi s₀) : 0 < sliceClock A s₀ η h s :=
    (mul_pos hc (hs₀.trans hs)).trans_le (hη s hs)
  have hcont : ContinuousOn (sliceParameterKernel A s₀ κ η h) (Ioi s₀) :=
    (hκcont.mul hηcont).inv₀ (fun s hs => (mul_pos (hpκ s hs) (hpη s hs)).ne')
  apply ((integrableOn_Ioi_rpow_of_lt
    (by norm_num : (-2 : ℝ) < -1) hs₀).const_mul (c⁻¹ ^ 2)).mono'
      (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hpp : 0 < sliceParameterKernel A s₀ κ η h s :=
    inv_pos.mpr (mul_pos (hpκ s hs) (hpη s hs))
  rw [Real.norm_eq_abs, abs_of_pos hpp]
  have hlow : (c * s) ^ 2 ≤ sliceClock A s₀ κ h s * sliceClock A s₀ η h s := by
    rw [pow_two]
    exact mul_le_mul (hκ s hs) (hη s hs) (mul_pos hc (hs₀.trans hs)).le (hpκ s hs).le
  calc
    sliceParameterKernel A s₀ κ η h s ≤ ((c * s) ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_pos (mul_pos hc (hs₀.trans hs))) hlow
    _ = _ := by
      rw [Real.rpow_neg (hs₀.trans hs).le, Real.rpow_two]
      simp [mul_pow, inv_pow, mul_comm]

theorem sliceTail_sub_eq_parameterKernel
    {A s₀ κ η : ℝ} {h : ℝ → ℝ}
    (hiκ : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀))
    (hiη : IntegrableOn (sliceIntegrand A s₀ η h) (Ioi s₀))
    (hκ : ∀ s ∈ Ioi s₀, sliceClock A s₀ κ h s ≠ 0)
    (hη : ∀ s ∈ Ioi s₀, sliceClock A s₀ η h s ≠ 0) :
    sliceTail A s₀ κ h - sliceTail A s₀ η h =
      (η - κ) * ∫ s in Ioi s₀, sliceParameterKernel A s₀ κ η h s := by
  unfold sliceTail
  rw [← integral_sub hiκ hiη, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  unfold sliceIntegrand sliceParameterKernel
  field_simp [hκ s hs, hη s hs]
  simp only [sliceClock]
  ring

theorem sliceParameterKernel_integral_bounds
    {A s₀ κ η c d : ℝ} {h : ℝ → ℝ}
    (hs₀ : 0 < s₀) (hc : 0 < c) (hd : 0 < d)
    (hκcont : ContinuousOn (sliceClock A s₀ κ h) (Ioi s₀))
    (hηcont : ContinuousOn (sliceClock A s₀ η h) (Ioi s₀))
    (hκ : ∀ s ∈ Ioi s₀,
      c * s ≤ sliceClock A s₀ κ h s ∧ sliceClock A s₀ κ h s ≤ d * s)
    (hη : ∀ s ∈ Ioi s₀,
      c * s ≤ sliceClock A s₀ η h s ∧ sliceClock A s₀ η h s ≤ d * s) :
    d⁻¹ ^ 2 * s₀⁻¹ ≤ ∫ s in Ioi s₀, sliceParameterKernel A s₀ κ η h s ∧
      (∫ s in Ioi s₀, sliceParameterKernel A s₀ κ η h s) ≤ c⁻¹ ^ 2 * s₀⁻¹ := by
  have hint := sliceParameterKernel_integrableOn hs₀ hc hκcont hηcont
    (fun s hs => (hκ s hs).1) (fun s hs => (hη s hs).1)
  have hid (x : ℝ) : (∫ s in Ioi s₀, x⁻¹ ^ 2 * s ^ (-2 : ℝ)) =
      x⁻¹ ^ 2 * s₀⁻¹ := by
    rw [integral_const_mul, integral_Ioi_rpow_neg_two hs₀]
  have hi (x : ℝ) := (integrableOn_Ioi_rpow_of_lt
    (by norm_num : (-2 : ℝ) < -1) hs₀).const_mul (x⁻¹ ^ 2)
  constructor
  · rw [← hid d]
    apply integral_mono_ae (hi d) hint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (sliceParameterKernel_bounds (hs₀.trans hs) hc hd (hκ s hs) (hη s hs)).1
  · rw [← hid c]
    apply integral_mono_ae hint (hi c)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (sliceParameterKernel_bounds (hs₀.trans hs) hc hd (hκ s hs) (hη s hs)).2

/-- Exact monotonicity and quantitative invertibility, derived by integrating
the positive parameter kernel of the actual clock. -/
theorem sliceTail_parameter_bounds
    {A s₀ κ η c d : ℝ} {h : ℝ → ℝ}
    (hs₀ : 0 < s₀) (hc : 0 < c) (hd : 0 < d) (hηκ : η ≤ κ)
    (hiκ : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀))
    (hiη : IntegrableOn (sliceIntegrand A s₀ η h) (Ioi s₀))
    (hκcont : ContinuousOn (sliceClock A s₀ κ h) (Ioi s₀))
    (hηcont : ContinuousOn (sliceClock A s₀ η h) (Ioi s₀))
    (hκ : ∀ s ∈ Ioi s₀,
      c * s ≤ sliceClock A s₀ κ h s ∧ sliceClock A s₀ κ h s ≤ d * s)
    (hη : ∀ s ∈ Ioi s₀,
      c * s ≤ sliceClock A s₀ η h s ∧ sliceClock A s₀ η h s ≤ d * s) :
    (κ - η) * (d⁻¹ ^ 2 * s₀⁻¹) ≤ sliceTail A s₀ η h - sliceTail A s₀ κ h ∧
      sliceTail A s₀ η h - sliceTail A s₀ κ h ≤ (κ - η) * (c⁻¹ ^ 2 * s₀⁻¹) := by
  rw [sliceTail_sub_eq_parameterKernel hiη hiκ
    (fun s hs => ((mul_pos hc (hs₀.trans hs)).trans_le (hη s hs).1).ne')
    (fun s hs => ((mul_pos hc (hs₀.trans hs)).trans_le (hκ s hs).1).ne')]
  have hb := sliceParameterKernel_integral_bounds hs₀ hc hd hηcont hκcont hη hκ
  exact ⟨mul_le_mul_of_nonneg_left hb.1 (sub_nonneg.mpr hηκ),
    mul_le_mul_of_nonneg_left hb.2 (sub_nonneg.mpr hηκ)⟩

theorem sliceTail_parameter_abs_le
    {A s₀ κ η c d : ℝ} {h : ℝ → ℝ}
    (hs₀ : 0 < s₀) (hc : 0 < c) (hd : 0 < d)
    (hiκ : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀))
    (hiη : IntegrableOn (sliceIntegrand A s₀ η h) (Ioi s₀))
    (hκcont : ContinuousOn (sliceClock A s₀ κ h) (Ioi s₀))
    (hηcont : ContinuousOn (sliceClock A s₀ η h) (Ioi s₀))
    (hκ : ∀ s ∈ Ioi s₀,
      c * s ≤ sliceClock A s₀ κ h s ∧ sliceClock A s₀ κ h s ≤ d * s)
    (hη : ∀ s ∈ Ioi s₀,
      c * s ≤ sliceClock A s₀ η h s ∧ sliceClock A s₀ η h s ≤ d * s) :
    |sliceTail A s₀ κ h - sliceTail A s₀ η h| ≤
      |κ - η| * (c⁻¹ ^ 2 * s₀⁻¹) := by
  rw [sliceTail_sub_eq_parameterKernel hiκ hiη
    (fun s hs => ((mul_pos hc (hs₀.trans hs)).trans_le (hκ s hs).1).ne')
    (fun s hs => ((mul_pos hc (hs₀.trans hs)).trans_le (hη s hs).1).ne')]
  have hb := sliceParameterKernel_integral_bounds hs₀ hc hd hκcont hηcont hκ hη
  have hnonneg : 0 ≤ ∫ s in Ioi s₀, sliceParameterKernel A s₀ κ η h s :=
    (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hs₀.le)).trans hb.1
  rw [abs_mul, abs_of_nonneg hnonneg, abs_sub_comm η κ]
  exact mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)

end HBL.Kinematic
