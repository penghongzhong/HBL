import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftRegularizedVolterra
import HBL.KummerOriginGreen.InverseLinearSourceRegularizedNoRadiusLoss
import Mathlib.Tactic

/-!
# True Cramer zero-left spectral Green response BELOW its moving left anchor

The physical backward overlap is [L/2,L], but the normalized Kummer
matching anchor is L/a. Earlier Volterra bounds were stated only for
r >= r0=L/a; substituting them below r0 would be invalid.

For the ORIGINAL exact zero-jet Cramer response anchored at a>0,
the constant singular coefficient cancels the source primitive at a
for EVERY positive r, even r<a. Direct interval additivity then
bounds both genuine Wronskian moments on [a/2,a]. The result needs
only an inverse-linear source on that backward interval and explicit
integrability of the true source densities, not a manufactured
radial envelope for the Green response, nor any Type-II rate.

A follow-up physical module must insert the source q=delta*u0 from the
same actual selected Hartree field and the genuine shell Fredholm bound.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Exact Cramer source-moment cancellation holds also to the LEFT of
the original zero-Cauchy-jet anchor. -/
theorem actual_Hartree_zero_left_original_Green_backward_identity
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C : ℝ) (_ha : 0 < a) (hab : a ≤ b)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) (r : ℝ) (hr : 0 < r) :
    (r : ℂ) * actualOriginMatchedKummerValue K a b F 0 0 r =
      K.y r * (originGreenCoeffA K b F r - originGreenCoeffA K b F a) +
        K.x r * originGreenCoeffB K a F r := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hSing :
      actualOriginMatchedSingularCoeff K a b F 0 0 =
        -originGreenCoeffA K b F a := by
    rw [actual_origin_matched_Kummer_singular_eq_obstruction K hK hab F 0 0]
    unfold actualMomentLockedIntervalObstruction actualOriginOutgoingTrace
    simp
  have hReg : actualOriginMatchedRegularCoeff K a b F 0 0 = 0 := by
    rw [actual_origin_matched_Kummer_regular_coefficient K a b F 0 0]
    simp
  unfold actualOriginMatchedKummerValue originGreenValue
  rw [hSing, hReg]
  simp only [zero_mul, add_zero]
  unfold originPhysicalValue
  field_simp [hrC]
  ring

/-- Backward true-Volterra value bound on [a/2,a]: no inverse moving
matching radius. Both source coefficient primitives are integrated
on the ACTUAL backward interval, rather than estimated globally. -/
theorem actual_Hartree_zero_left_original_Green_backward_inverse_linear_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G M : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc (a / 2) a, ‖F x‖ ≤ M / x)
    (r : ℝ) (hr : r ∈ Icc (a / 2) a)
    (hIntA1 : IntervalIntegrable (originGreenSourceA K F) volume r a)
    (hIntA2 : IntervalIntegrable (originGreenSourceA K F) volume a b) :
    ‖actualOriginMatchedKummerValue K a b F 0 0 r‖ ≤
      2 * G ^ 2 * M := by
  have hHalf : 0 < a / 2 := by positivity
  have hrpos : 0 < r := hHalf.trans_le hr.1
  have hrScale : r ∈ Icc 0 scale :=
    ⟨hrpos.le, hr.2.trans (hab.trans hb)⟩
  have hModes := hbound r hrScale
  have hAint :=
    intervalIntegral.integral_add_adjacent_intervals hIntA1 hIntA2
  have hAeq :
      originGreenCoeffA K b F r - originGreenCoeffA K b F a =
        ∫ x in r..a, originGreenSourceA K F x := by
    unfold originGreenCoeffA
    rw [← hAint]
    abel
  have hA :
      ‖originGreenCoeffA K b F r - originGreenCoeffA K b F a‖ ≤
        (G * M) * (a - r) := by
    rw [hAeq]
    have h :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := r) (b := a) (C := G * M) (fun x hx => by
          rw [uIoc_of_le hr.2] at hx
          have hxI : x ∈ Icc (a / 2) a :=
            ⟨hr.1.trans hx.1.le, hx.2⟩
          exact (originGreen_inverse_linear_source_regularized_uniform
            K G M hG hM hbound F x
            ⟨hHalf.trans_le hxI.1, hxI.2.trans (hab.trans hb)⟩
            (hF x hxI)).1)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hr.2)] using h
  have hB :
      ‖originGreenCoeffB K a F r‖ ≤ (G * M) * (a - r) := by
    unfold originGreenCoeffB
    have h :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := a) (b := r) (C := G * M) (fun x hx => by
          rw [uIoc_of_ge hr.2] at hx
          have hxI : x ∈ Icc (a / 2) a :=
            ⟨hr.1.trans hx.1.le, hx.2⟩
          exact (originGreen_inverse_linear_source_regularized_uniform
            K G M hG hM hbound F x
            ⟨hHalf.trans_le hxI.1, hxI.2.trans (hab.trans hb)⟩
            (hF x hxI)).2)
    simpa only [abs_of_nonpos (sub_nonpos.mpr hr.2), neg_sub] using h
  have hWeighted := actual_Hartree_zero_left_original_Green_backward_identity
    K a b C ha hab hK F r hrpos
  have hCr : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  have hC0 : 0 ≤ 2 * G ^ 2 * M := by positivity
  have hRatio : a - r ≤ r := by
    have h2 := hr.1
    linarith
  have hProduct :
      ‖(r : ℂ) * actualOriginMatchedKummerValue K a b F 0 0 r‖ ≤
        (2 * G ^ 2 * M) * (a - r) := by
    rw [hWeighted]
    calc
      ‖K.y r * (originGreenCoeffA K b F r -
            originGreenCoeffA K b F a) +
          K.x r * originGreenCoeffB K a F r‖ ≤
        ‖K.y r‖ * ‖originGreenCoeffA K b F r -
          originGreenCoeffA K b F a‖ +
          ‖K.x r‖ * ‖originGreenCoeffB K a F r‖ := by
        simpa only [norm_mul] using
          (norm_add_le
            (K.y r * (originGreenCoeffA K b F r -
              originGreenCoeffA K b F a))
            (K.x r * originGreenCoeffB K a F r))
      _ ≤ G * ((G * M) * (a - r)) +
          G * ((G * M) * (a - r)) :=
        add_le_add
          (mul_le_mul hModes.1 hA (norm_nonneg _) hG)
          (mul_le_mul hModes.2 hB (norm_nonneg _) hG)
      _ = (2 * G ^ 2 * M) * (a - r) := by ring
  have hDivide :
      ‖actualOriginMatchedKummerValue K a b F 0 0 r‖ ≤
        ((2 * G ^ 2 * M) * (a - r)) / r := by
    apply (le_div_iff₀ hrpos).2
    simpa only [norm_mul, hCr, mul_comm] using hProduct
  calc
    ‖actualOriginMatchedKummerValue K a b F 0 0 r‖ ≤
        ((2 * G ^ 2 * M) * (a - r)) / r := hDivide
    _ ≤ 2 * G ^ 2 * M := by
      apply (div_le_iff₀ hrpos).2
      exact mul_le_mul_of_nonneg_left hRatio hC0

end HBL.TypeIIDynamicSelection
