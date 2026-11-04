import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCoupledTraceEstimate
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedProjectionAsymptotics
import HBL.TypeIIDynamicSelection.ComplexTwoColumnDeterminantBound

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.Kummer

def actualMomentLockedFullColumnBudget
    (L c : ℝ) (hL : 0 < L) (a B H C0 Msrc : ℝ) : ℝ :=
  C0 * L ^ 2 / a ^ 2 + 2 * C0 * B ^ 2 / L ^ 2 +
    C0 * Msrc * B ^ 3 * (a * |c|) +
      actualMomentLockedCoupledTraceBudget L c hL a H C0

/-- Both full columns, with their actual Fredholm traces retained, approach
the actual origin-gauge reference pair. The error is proved from the physical
sources and the reconstructed-source moments, not assumed for either column. -/
theorem actual_Hartree_moment_locked_full_column_bounds
    (Msrc : ℝ) (hMsrc : 0 < Msrc)
    (hClose : ∀ c r : ℝ, 0 < r →
      |actualMomentLockedScaleProfile c r - dilationGenerator bubble r| ≤ Msrc * |c| ∧
      |actualMomentLockedCore c r - bubble r| ≤ Msrc * |c|)
    {mu theta R B : ℝ} (K : OriginKummerPair mu theta R)
    (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (_hB : 0 < B) (hBR : B < R)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (L c a : ℝ) (hL : 2 < L) (ha : 0 < a) (hLB : L / a ≤ B) :
    let hLp : 0 < L := lt_trans (by norm_num : (0 : ℝ) < 2) hL
    let H := (D + 1) * G
    let C0 := 1 + H * B ^ 2
    let cols := actualMomentLockedCoupledColumns K L c hLp a (L / a) B
    let A := originKummerReferenceIntegral K B
    ‖cols.1 / (a : ℂ) + Complex.I * A / 2‖ ≤
      actualMomentLockedFullColumnBudget L c hLp a B H C0 Msrc ∧
    ‖cols.2 / (a : ℂ) - A‖ ≤
      actualMomentLockedFullColumnBudget L c hLp a B H C0 Msrc := by
  dsimp only
  have hLp : 0 < L := by linarith
  let H := (D + 1) * G
  let C0 := 1 + H * B ^ 2
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hx (r : ℝ) (hr : r ∈ Icc 0 B) : ‖K.x r‖ ≤ C0 * r := by
    have hj := (origin_kummer_regular_jet_bound K D G hD hG hcoeff hbound
      r ⟨hr.1, hr.2.trans hBR.le⟩).1
    have ht := norm_add_le (K.x r - (r : ℂ)) (r : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1] at ht
    have hs := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hr.1 hr.2 2) (mul_nonneg hH hr.1)
    dsimp [C0, H] at hs ⊢
    nlinarith
  let C := G * (1 / (L / a) + 1 / (L / a) ^ 2) + B ^ 2 + 1
  have hK : OriginBasisOn K (L / a) B C :=
    origin_kummer_annulus_bound K (L / a) B G (div_pos hLp ha) hBR hG hbound
  have hp := actual_Hartree_moment_locked_full_projection_asymptotics_of_uniform_close
    Msrc hMsrc hClose K a L B C C0 c ha hLp hLB hBR.le hC0 hK hx
  have ht := actual_Hartree_moment_locked_outgoing_trace_bounds K D G hD hG
    hBR.le hcoeff hbound L c a hL ha hLB
  dsimp only at ht
  let Jb := actualMomentLockedScaleResponseJet L c hLp a (L / a)
  let Jw := actualMomentLockedPhaseResponseJet L c hLp a (L / a)
  let A := originKummerReferenceIntegral K B
  have hbEq : (actualMomentLockedCoupledColumns K L c hLp a (L / a) B).1 /
        (a : ℂ) + Complex.I * A / 2 =
      actualOriginOutgoingTrace K (L / a) Jb.1 Jb.2 / (a : ℂ) +
        ((a : ℂ)⁻¹ * originGreenCoeffA K B
          (actualMomentLockedScaledScaleSource a c) (L / a) + Complex.I * A / 2) := by
    dsimp [actualMomentLockedCoupledColumns, Jb]
    ring
  have hwEq : (actualMomentLockedCoupledColumns K L c hLp a (L / a) B).2 /
        (a : ℂ) - A =
      actualOriginOutgoingTrace K (L / a) Jw.1 Jw.2 / (a : ℂ) +
        ((a : ℂ)⁻¹ * originGreenCoeffA K B
          (actualMomentLockedScaledPhaseSource a c) (L / a) - A) := by
    dsimp [actualMomentLockedCoupledColumns, Jw]
    ring
  constructor
  · rw [hbEq]
    exact (norm_add_le _ _).trans
      ((add_le_add ht.1 hp.1).trans_eq (by
        dsimp [actualMomentLockedFullColumnBudget, H, C0]; ring))
  · rw [hwEq]
    exact (norm_add_le _ _).trans
      ((add_le_add ht.2 hp.2).trans_eq (by
        dsimp [actualMomentLockedFullColumnBudget, H, C0]; ring))

private theorem real_column_det_rescale (a : ℝ) (ha : a ≠ 0) (b w : ℂ) :
    b.re * w.im - w.re * b.im = a ^ 2 *
      ((b / (a : ℂ)).re * (w / (a : ℂ)).im -
        (w / (a : ℂ)).re * (b / (a : ℂ)).im) := by
  simp [Complex.div_re, Complex.div_im, Complex.normSq_apply]
  field_simp [ha]

/-- A quantitative lower bound for the SAME complete physical matrix.
The reference nonzero bound is derived from the actual origin ODE. The
explicit budget premise is discharged by the physical parameter-region
theorem, using the derived growth of the actual Fredholm moments. -/
theorem actual_Hartree_moment_locked_coupled_determinant_lower_bound_of_budget
    (Msrc : ℝ) (hMsrc : 0 < Msrc)
    (hClose : ∀ c r : ℝ, 0 < r →
      |actualMomentLockedScaleProfile c r - dilationGenerator bubble r| ≤ Msrc * |c| ∧
      |actualMomentLockedCore c r - bubble r| ≤ Msrc * |c|)
    {mu theta R B : ℝ} (K : OriginKummerPair mu theta R)
    (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B) (hBR : B < R)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1)
    (L c a : ℝ) (hL : 2 < L) (ha : 0 < a) (hLB : L / a ≤ B)
    (hBudget : actualMomentLockedFullColumnBudget L c
      (lt_trans (by norm_num : (0 : ℝ) < 2) hL) a B ((D + 1) * G)
      (1 + (D + 1) * G * B ^ 2) Msrc ≤ B ^ 2 / 16) :
    let hLp : 0 < L := lt_trans (by norm_num : (0 : ℝ) < 2) hL
    a ^ 2 * B ^ 4 / 256 ≤
      actualMomentLockedCoupledDeterminant K L c hLp a (L / a) B ∧
    0 < actualMomentLockedCoupledDeterminant K L c hLp a (L / a) B := by
  dsimp only
  have hLp : 0 < L := by linarith
  let cols := actualMomentLockedCoupledColumns K L c hLp a (L / a) B
  let A := originKummerReferenceIntegral K B
  let E := actualMomentLockedFullColumnBudget L c hLp a B ((D + 1) * G)
    (1 + (D + 1) * G * B ^ 2) Msrc
  have hcols := actual_Hartree_moment_locked_full_column_bounds
    Msrc hMsrc hClose K D G hD hG hB hBR hcoeff hbound L c a hL ha hLB
  dsimp only at hcols
  have hA : B ^ 2 / 4 ≤ ‖A‖ :=
    origin_kummer_reference_integral_lower_bound K D G hD hG hB.le hBR.le
      hcoeff hbound hsmallB
  have hSmall : E ≤ ‖A‖ / 4 := by dsimp [E]; linarith
  have hdet := complex_two_column_determinant_lower_bound A
    (cols.1 / (a : ℂ)) (cols.2 / (a : ℂ)) E hcols.1 hcols.2 hSmall
  have hASq : B ^ 4 / 16 ≤ ‖A‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA)
      (show 0 ≤ ‖A‖ + B ^ 2 / 4 by positivity)]
  have hScaled := mul_le_mul_of_nonneg_left hdet (sq_nonneg a)
  have hRescale := real_column_det_rescale a ha.ne' cols.1 cols.2
  have hLower : a ^ 2 * B ^ 4 / 256 ≤
      actualMomentLockedCoupledDeterminant K L c hLp a (L / a) B := by
    change a ^ 2 * B ^ 4 / 256 ≤ cols.1.re * cols.2.im - cols.2.re * cols.1.im
    have hAA := mul_le_mul_of_nonneg_left hASq (sq_nonneg a)
    nlinarith
  exact ⟨hLower, lt_of_lt_of_le (by positivity) hLower⟩

end HBL.TypeIIDynamicSelection
