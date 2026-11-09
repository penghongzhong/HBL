import HBL.TypeIIDynamicSelection.ActualHartreeBackwardZeroLeftSpectralVolterra
import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftRegularizedVolterraSlope
import HBL.KummerOriginGreen.InverseLinearSourceRegularizedNoRadiusLoss
import Mathlib.Tactic

/-!
# Genuine backward original Green slope below the original Cramer anchor

The original zero-jet Cramer correction has a regularized r²*u' formula
even for r<a. The Wronskian coefficient cancellation is independent of
the evaluation radius; the source moments are integrated in the correct
backward orientation on [a/2,a]. No a^(-1) or a^(-2) coefficient appears
in the final weighted C¹ estimate.

The source F is the actual original zero-jet Green source, not an
abstract linear right-inverse. Only its inverse-linear size and true
interval integrability are inputs. No parameter time order is claimed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The exact radial-conjugated derivative identity remains valid to
the LEFT of the zero-Cauchy matching anchor. -/
theorem actual_Hartree_zero_left_backward_original_Green_slope_identity
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) (r : ℝ) (hr : 0 < r) :
    (r : ℂ) ^ 2 * actualOriginMatchedKummerSlope K a b F 0 0 r =
      ((r : ℂ) * K.dy r - K.y r) *
        (originGreenCoeffA K b F r - originGreenCoeffA K b F a) +
      ((r : ℂ) * K.dx r - K.x r) *
        originGreenCoeffB K a F r := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hSing :
      actualOriginMatchedSingularCoeff K a b F 0 0 =
        -originGreenCoeffA K b F a := by
    rw [actual_origin_matched_Kummer_singular_eq_obstruction
      K hK hab F 0 0]
    unfold actualMomentLockedIntervalObstruction actualOriginOutgoingTrace
    simp
  have hReg : actualOriginMatchedRegularCoeff K a b F 0 0 = 0 := by
    rw [actual_origin_matched_Kummer_regular_coefficient K a b F 0 0]
    simp
  unfold actualOriginMatchedKummerSlope originGreenSlope
  rw [hSing, hReg]
  simp only [zero_mul, add_zero]
  unfold originPhysicalSlope
  field_simp [hrC]
  ring

/-- True backward original Green derivative, with no negative power of
the original small matching radius. -/
theorem actual_Hartree_zero_left_backward_original_Green_slope_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G M : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C)
    (hModes : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc (a / 2) a, ‖F x‖ ≤ M / x)
    (r : ℝ) (hr : r ∈ Icc (a / 2) a)
    (hIntA1 : IntervalIntegrable (originGreenSourceA K F) volume r a)
    (hIntA2 : IntervalIntegrable (originGreenSourceA K F) volume a b) :
    ‖(r : ℂ) ^ 2 * actualOriginMatchedKummerSlope K a b F 0 0 r‖ ≤
      2 * (a + 1) * G ^ 2 * M * (a - r) := by
  have hHalf : 0 < a / 2 := by positivity
  have hrPos : 0 < r := hHalf.trans_le hr.1
  have hrScale : r ∈ Icc 0 scale :=
    ⟨hrPos.le, hr.2.trans (hab.trans hb)⟩
  have hAt := hModes r hrScale
  have hPairs : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G := by
    intro x hx
    exact ⟨(hModes x hx).1, (hModes x hx).2.2.1⟩
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
            K G M hG hM hPairs F x
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
            K G M hG hM hPairs F x
            ⟨hHalf.trans_le hxI.1, hxI.2.trans (hab.trans hb)⟩
            (hF x hxI)).2)
    simpa only [abs_of_nonpos (sub_nonpos.mpr hr.2), neg_sub] using h
  have hBig : 0 ≤ (a + 1) * G := by positivity
  have hMode (p dp : ℝ → ℂ)
      (hp : ‖p r‖ ≤ G) (hdp : ‖dp r‖ ≤ G) :
      ‖(r : ℂ) * dp r - p r‖ ≤ (a + 1) * G := by
    calc
      _ ≤ ‖(r : ℂ) * dp r‖ + ‖p r‖ := norm_sub_le _ _
      _ = r * ‖dp r‖ + ‖p r‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrPos]
      _ ≤ r * G + G :=
        add_le_add (mul_le_mul_of_nonneg_left hdp hrPos.le) hp
      _ ≤ a * G + G :=
        add_le_add_left (mul_le_mul_of_nonneg_right hr.2 hG) G
      _ = (a + 1) * G := by ring
  have hY : ‖(r : ℂ) * K.dy r - K.y r‖ ≤ (a + 1) * G :=
    hMode K.y K.dy hAt.1 hAt.2.1
  have hX : ‖(r : ℂ) * K.dx r - K.x r‖ ≤ (a + 1) * G :=
    hMode K.x K.dx hAt.2.2.1 hAt.2.2.2
  have hId := actual_Hartree_zero_left_backward_original_Green_slope_identity
    K a b C ha hab hK F r hrPos
  rw [hId]
  calc
    ‖((r : ℂ) * K.dy r - K.y r) *
        (originGreenCoeffA K b F r - originGreenCoeffA K b F a) +
      ((r : ℂ) * K.dx r - K.x r) *
        originGreenCoeffB K a F r‖ ≤
      ‖(r : ℂ) * K.dy r - K.y r‖ *
          ‖originGreenCoeffA K b F r - originGreenCoeffA K b F a‖ +
        ‖(r : ℂ) * K.dx r - K.x r‖ *
          ‖originGreenCoeffB K a F r‖ := by
        simpa only [norm_mul] using
          (norm_add_le
            (((r : ℂ) * K.dy r - K.y r) *
              (originGreenCoeffA K b F r - originGreenCoeffA K b F a))
            (((r : ℂ) * K.dx r - K.x r) *
              originGreenCoeffB K a F r))
    _ ≤ ((a + 1) * G) * ((G * M) * (a - r)) +
        ((a + 1) * G) * ((G * M) * (a - r)) :=
      add_le_add
        (mul_le_mul hY hA (norm_nonneg _) hBig)
        (mul_le_mul hX hB (norm_nonneg _) hBig)
    _ = 2 * (a + 1) * G ^ 2 * M * (a - r) := by ring

end HBL.TypeIIDynamicSelection
