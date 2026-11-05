import HBL.TypeIIDynamicSelection.ActualHartreeGeneralMatchedShell

/-!
# Outward growth of the same actual matched Kummer field

The forward formula cancels the spurious B/r0 loss in the singular
coefficient before taking absolute values. The field, its coefficients
and all source integrals are exactly those used by the accepted matching
construction. No independent exterior profile or extra free coefficient
is introduced. This is a frozen spatial estimate, not the full PDE step.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

private theorem exterior_inverse_wronskian_norm
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r : ℝ) (hr : 0 < r) (hrs : r ≤ scale) :
    ‖(originGreenWronskian K r)⁻¹‖ = r ^ 2 := by
  have hW : originGreenWronskian K r =
      (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) :=
    origin_physical_wronskian_exact K ⟨hr.le, hrs⟩ hr.ne'
  have he : ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hW, norm_inv, norm_mul, norm_pow, norm_inv, he, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  simp

/-- Forward variation of constants for the SAME endpoint-matched field.
The integral from r0 to r, not an independently normalized Green solution,
is what removes the artificial upper-endpoint amplification. -/
theorem actual_matched_Kummer_forward_formula
    {mu theta scale r0 B C : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K r0 B C) (hOrder : r0 ≤ B)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume r0 B)
    (U DU : ℂ) (r : ℝ) (hr : r ∈ Icc r0 B) :
    actualOriginMatchedKummerValue K r0 B F U DU r =
      originPhysicalValue K.y r *
        (actualOriginOutgoingTrace K r0 U DU -
          ∫ s in r0..r, originGreenSourceA K F s) +
      originPhysicalValue K.x r *
        (actualOriginMatchedRegularCoeff K r0 B F U DU +
          originGreenCoeffB K r0 F r) := by
  have hIA := (actual_origin_Green_source_integrability K hK hOrder F hF).1
  have hLeft : IntervalIntegrable (originGreenSourceA K F) volume r0 r :=
    hIA.mono_set (by
      rw [uIcc_of_le hr.1, uIcc_of_le hOrder]
      exact Icc_subset_Icc_right hr.2)
  have hRight : IntervalIntegrable (originGreenSourceA K F) volume r B :=
    hIA.mono_set (by
      rw [uIcc_of_le hr.2, uIcc_of_le hOrder]
      exact Icc_subset_Icc_left hr.1)
  have hSplit := intervalIntegral.integral_add_adjacent_intervals hLeft hRight
  have hs := actual_origin_matched_Kummer_singular_eq_obstruction K hK hOrder F U DU
  unfold actualOriginMatchedKummerValue originGreenValue
  rw [hs]
  unfold actualMomentLockedIntervalObstruction originGreenCoeffA
  linear_combination originPhysicalValue K.y r * hSplit

/-- A source-independent constant for the forward actual origin gauge. -/
def actualMatchedExteriorGrowthConstant (D G B : ℝ) : ℝ :=
  1 + 2 * G * ((D + 1) * G) + 6 * G * (1 + (D + 1) * G * B ^ 2)

/-- True outward growth for arbitrary inverse-square forcing. In particular
there is no coefficient of size B/r0 multiplying the initial data. The
right side is homogeneous in the actual initial jet and source envelope. -/
theorem actual_matched_Kummer_outward_growth
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B r0 : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hr0 : 0 < r0) (hOrder : r0 ≤ B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (F : ℝ → ℂ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hF : IntervalIntegrable F volume r0 B)
    (hEnvelope : ∀ s ∈ Icc r0 B, ‖F s‖ ≤ Q / s ^ 2)
    (U DU : ℂ) (r : ℝ) (hr : r ∈ Icc r0 B) :
    ‖actualOriginMatchedKummerValue K r0 B F U DU r‖ ≤
      actualMatchedExteriorGrowthConstant D G B *
        (‖U‖ + r0 * ‖DU‖ + Q) * (r / r0) := by
  let H := (D + 1) * G
  let C0 := 1 + (D + 1) * G * B ^ 2
  let S := ‖U‖ + r0 * ‖DU‖ + Q
  let A := actualOriginOutgoingTrace K r0 U DU
  let beta := actualOriginMatchedRegularCoeff K r0 B F U DU
  let I := ∫ s in r0..r, originGreenSourceA K F s
  let J := originGreenCoeffB K r0 F r
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hv0 : 0 ≤ r0 * ‖DU‖ := mul_nonneg hr0.le (norm_nonneg _)
  have hU : ‖U‖ ≤ S := by dsimp [S]; linarith only [hv0, hQ]
  have hDU : r0 * ‖DU‖ ≤ S := by dsimp [S]; linarith only [norm_nonneg U, hQ]
  have hQS : Q ≤ S := by dsimp [S]; linarith only [norm_nonneg U, hv0]
  have hrp : 0 < r := hr0.trans_le hr.1
  have hr0One : r0 ≤ 1 := hOrder.trans hBOne
  have hRatio : 1 ≤ r / r0 := (le_div_iff₀ hr0).2 (by simpa using hr.1)
  have hSr : S ≤ S * (r / r0) := le_mul_of_one_le_right hS hRatio
  have hK := origin_kummer_annulus_bound K r0 B G hr0 hBR hG hbound
  have hForward := actual_matched_Kummer_forward_formula K hK hOrder F hF U DU r hr
  have hRegular (s : ℝ) (hs : s ∈ Icc r0 B) :
      ‖originPhysicalValue K.x s‖ ≤ C0 ∧
      ‖originPhysicalSlope K.x K.dx s‖ ≤ 2 * H * s :=
    origin_kummer_regular_physical_bound K D G hD hG hBR.le hcoeff hbound s
      ⟨hr0.trans_le hs.1, hs.2⟩
  have hSingular (s : ℝ) (hs : s ∈ Icc r0 B) :
      ‖originPhysicalValue K.y s‖ ≤ G / s ∧
      ‖originPhysicalSlope K.y K.dy s‖ ≤ G / s + G / s ^ 2 := by
    have hsp : 0 < s := hr0.trans_le hs.1
    have hb := hbound s ⟨hsp.le, hs.2.trans hBR.le⟩
    constructor
    · rw [originPhysicalValue, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
      exact div_le_div_of_nonneg_right hb.1 hsp.le
    · unfold originPhysicalSlope
      calc
        _ ≤ ‖K.dy s / (s : ℂ)‖ + ‖K.y s / (s : ℂ) ^ 2‖ := norm_sub_le _ _
        _ = ‖K.dy s‖ / s + ‖K.y s‖ / s ^ 2 := by
          simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
        _ ≤ G / s + G / s ^ 2 := add_le_add
          (div_le_div_of_nonneg_right hb.2.1 hsp.le)
          (div_le_div_of_nonneg_right hb.1 (sq_nonneg s))
  have h0 : r0 ∈ Icc r0 B := ⟨le_rfl, hOrder⟩
  have hInv0 := exterior_inverse_wronskian_norm K r0 hr0 (hOrder.trans hBR.le)
  have hA : ‖A‖ ≤ (2 * H * ‖U‖ + C0 * (r0 * ‖DU‖)) * r0 := by
    have hRaw : ‖A‖ ≤ (‖U‖ * (2 * H * r0) + ‖DU‖ * C0) * r0 ^ 2 := by
      dsimp [A]
      unfold actualOriginOutgoingTrace
      rw [div_eq_mul_inv, norm_mul, hInv0]
      exact mul_le_mul_of_nonneg_right
        (((norm_sub_le _ _).trans_eq (by simp only [norm_mul])).trans
          (add_le_add (mul_le_mul_of_nonneg_left (hRegular r0 h0).2 (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hRegular r0 h0).1 (norm_nonneg _)))) (sq_nonneg r0)
    have hsq : r0 ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr0One
    have hmul := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ 2 * H * ‖U‖ * r0 by positivity)
    nlinarith only [hRaw, hmul]
  have hBeta : ‖beta‖ ≤ G * (r0 * ‖DU‖) + 2 * G * ‖U‖ := by
    have hRaw : ‖beta‖ ≤
        ((G / r0) * ‖DU‖ + (G / r0 + G / r0 ^ 2) * ‖U‖) * r0 ^ 2 := by
      dsimp [beta]
      rw [actual_origin_matched_Kummer_regular_coefficient, div_eq_mul_inv, norm_mul, hInv0]
      exact mul_le_mul_of_nonneg_right
        (((norm_sub_le _ _).trans_eq (by simp only [norm_mul])).trans
          (add_le_add (mul_le_mul_of_nonneg_right (hSingular r0 h0).1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (hSingular r0 h0).2 (norm_nonneg _)))) (sq_nonneg r0)
    have heq : ((G / r0) * ‖DU‖ + (G / r0 + G / r0 ^ 2) * ‖U‖) * r0 ^ 2 =
        G * (r0 * ‖DU‖) + G * (r0 + 1) * ‖U‖ := by field_simp [hr0.ne']
    rw [heq] at hRaw
    have hcoef : G * (r0 + 1) ≤ 2 * G :=
      (mul_le_mul_of_nonneg_left (by linarith : r0 + 1 ≤ 2) hG).trans_eq (by ring)
    exact hRaw.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)))
  have hDensity (s : ℝ) (hs : s ∈ Icc r0 B) :
      ‖originGreenSourceA K F s‖ ≤ C0 * Q ∧
      ‖originGreenSourceB K F s‖ ≤ G * Q / r0 := by
    have hsp : 0 < s := hr0.trans_le hs.1
    have hInv := exterior_inverse_wronskian_norm K s hsp (hs.2.trans hBR.le)
    constructor
    · rw [originGreenSourceA, div_eq_mul_inv, norm_mul, norm_mul, hInv]
      calc
        _ ≤ C0 * (Q / s ^ 2) * s ^ 2 := mul_le_mul_of_nonneg_right
          (mul_le_mul (hRegular s hs).1 (hEnvelope s hs) (norm_nonneg _) hC0) (sq_nonneg s)
        _ = _ := by field_simp [hsp.ne']
    · rw [originGreenSourceB, div_eq_mul_inv, norm_mul, norm_mul, hInv]
      calc
        _ ≤ (G / s) * (Q / s ^ 2) * s ^ 2 := mul_le_mul_of_nonneg_right
          (mul_le_mul (hSingular s hs).1 (hEnvelope s hs) (norm_nonneg _) (by positivity))
          (sq_nonneg s)
        _ = G * Q / s := by field_simp [hsp.ne']
        _ ≤ G * Q / r0 := div_le_div_of_nonneg_left (mul_nonneg hG hQ) hr0 hs.1
  have hI : ‖I‖ ≤ C0 * Q * r := by
    have hi : ‖I‖ ≤ (C0 * Q) * |r - r0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le hr.1] at hs
      exact (hDensity s ⟨hs.1.le, hs.2.trans hr.2⟩).1
    rw [abs_of_nonneg (sub_nonneg.mpr hr.1)] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0 hQ))
  have hJ : ‖J‖ ≤ (G * Q / r0) * r := by
    have hj : ‖J‖ ≤ (G * Q / r0) * |r - r0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le hr.1] at hs
      exact (hDensity s ⟨hs.1.le, hs.2.trans hr.2⟩).2
    rw [abs_of_nonneg (sub_nonneg.mpr hr.1)] at hj
    exact hj.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hPhiA : ‖originPhysicalValue K.y r‖ * ‖A‖ ≤ G * (2 * H + C0) * S * (r / r0) := by
    calc
      _ ≤ (G / r0) * ((2 * H * ‖U‖ + C0 * (r0 * ‖DU‖)) * r0) :=
        mul_le_mul ((hSingular r hr).1.trans (div_le_div_of_nonneg_left hG hr0 hr.1))
          hA (norm_nonneg _) (by positivity)
      _ = G * (2 * H * ‖U‖ + C0 * (r0 * ‖DU‖)) := by field_simp [hr0.ne']
      _ ≤ G * (2 * H * S + C0 * S) := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hU (by positivity))
          (mul_le_mul_of_nonneg_left hDU hC0)) hG
      _ = (G * (2 * H + C0)) * S := by ring
      _ ≤ (G * (2 * H + C0)) * (S * (r / r0)) :=
        mul_le_mul_of_nonneg_left hSr (by positivity)
      _ = _ := by ring
  have hPhiI : ‖originPhysicalValue K.y r‖ * ‖I‖ ≤ G * C0 * S * (r / r0) := by
    calc
      _ ≤ (G / r) * (C0 * Q * r) := mul_le_mul (hSingular r hr).1 hI
        (norm_nonneg _) (by positivity)
      _ = G * C0 * Q := by field_simp [hrp.ne']
      _ ≤ G * C0 * S := mul_le_mul_of_nonneg_left hQS (mul_nonneg hG hC0)
      _ ≤ (G * C0) * (S * (r / r0)) := mul_le_mul_of_nonneg_left hSr (mul_nonneg hG hC0)
      _ = _ := by ring
  have hPsiBeta : ‖originPhysicalValue K.x r‖ * ‖beta‖ ≤ 3 * G * C0 * S * (r / r0) := by
    calc
      _ ≤ C0 * (G * (r0 * ‖DU‖) + 2 * G * ‖U‖) :=
        mul_le_mul (hRegular r hr).1 hBeta (norm_nonneg _) hC0
      _ ≤ C0 * (G * S + 2 * G * S) := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hDU hG)
          (mul_le_mul_of_nonneg_left hU (by positivity))) hC0
      _ = (3 * G * C0) * S := by ring
      _ ≤ (3 * G * C0) * (S * (r / r0)) := mul_le_mul_of_nonneg_left hSr (by positivity)
      _ = _ := by ring
  have hPsiJ : ‖originPhysicalValue K.x r‖ * ‖J‖ ≤ G * C0 * S * (r / r0) := by
    calc
      _ ≤ C0 * ((G * Q / r0) * r) := mul_le_mul (hRegular r hr).1 hJ (norm_nonneg _) hC0
      _ = (G * C0 * (r / r0)) * Q := by ring
      _ ≤ (G * C0 * (r / r0)) * S := mul_le_mul_of_nonneg_left hQS (by positivity)
      _ = _ := by ring
  rw [hForward]
  calc
    _ ≤ ‖originPhysicalValue K.y r‖ * (‖A‖ + ‖I‖) +
        ‖originPhysicalValue K.x r‖ * (‖beta‖ + ‖J‖) := by
      exact (norm_add_le _ _).trans (add_le_add
        (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
        (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)))
    _ = (‖originPhysicalValue K.y r‖ * ‖A‖ + ‖originPhysicalValue K.y r‖ * ‖I‖) +
        (‖originPhysicalValue K.x r‖ * ‖beta‖ + ‖originPhysicalValue K.x r‖ * ‖J‖) := by ring
    _ ≤ (G * (2 * H + C0) * S * (r / r0) + G * C0 * S * (r / r0)) +
        (3 * G * C0 * S * (r / r0) + G * C0 * S * (r / r0)) :=
      add_le_add (add_le_add hPhiA hPhiI) (add_le_add hPsiBeta hPsiJ)
    _ = (2 * G * H + 6 * G * C0) * S * (r / r0) := by ring
    _ ≤ (1 + 2 * G * H + 6 * G * C0) * S * (r / r0) := by
      have hp : 0 ≤ S * (r / r0) := by positivity
      nlinarith only [hp]
    _ = _ := rfl

end HBL.TypeIIDynamicSelection
