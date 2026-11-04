import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCoupledCancellation

/-!
Quantitative inversion of the ACTUAL complete moment-locked matrix.
The original source and the same normalized inner Fredholm jet determine
the baseline obstruction Z. The two actual full columns have size a*B^2,
and their already proved determinant has size a^2*B^4. Consequently the
real speed increments cost at most 1024*|Z|/(a*B^2).

The physical parameter region is obtained from the existing source,
fixed-inverse moment and full-column estimates. No nonzero determinant,
independent trace, or replacement of |Z| by an inner source norm is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.Kummer

private theorem real_cross_numerator_bound (w Z : ℂ) :
    |w.re * Z.im - w.im * Z.re| ≤ 2 * ‖w‖ * ‖Z‖ := by
  calc
    _ ≤ |w.re * Z.im| + |w.im * Z.re| := abs_sub _ _
    _ = |w.re| * |Z.im| + |w.im| * |Z.re| := by rw [abs_mul, abs_mul]
    _ ≤ ‖w‖ * ‖Z‖ + ‖w‖ * ‖Z‖ := add_le_add
      (mul_le_mul (Complex.abs_re_le_norm w) (Complex.abs_im_le_norm Z)
        (abs_nonneg _) (norm_nonneg _))
      (mul_le_mul (Complex.abs_im_le_norm w) (Complex.abs_re_le_norm Z)
        (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

private theorem actual_columns_cancellation_bound
    (a B : ℝ) (ha : 0 < a) (hB : 0 < B) (b w Z : ℂ) (p : ℝ × ℝ)
    (hb : ‖b‖ ≤ a * B ^ 2) (hw : ‖w‖ ≤ a * B ^ 2)
    (hdet : a ^ 2 * B ^ 4 / 256 ≤ b.re * w.im - w.re * b.im)
    (hcancel : Z + (p.1 : ℂ) * b + (p.2 : ℂ) * w = 0) :
    |p.1| + |p.2| ≤ 1024 / (a * B ^ 2) * ‖Z‖ := by
  let d : ℝ := b.re * w.im - w.re * b.im
  have hd : 0 < d := lt_of_lt_of_le (by positivity) hdet
  have hr := congrArg Complex.re hcancel
  have hi := congrArg Complex.im hcancel
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, zero_mul, sub_zero] at hr
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_im, zero_mul, add_zero] at hi
  have hp1 : p.1 * d = w.re * Z.im - w.im * Z.re := by
    dsimp only [d]
    linear_combination w.im * hr - w.re * hi
  have hp2 : p.2 * d = b.im * Z.re - b.re * Z.im := by
    dsimp only [d]
    linear_combination b.re * hi - b.im * hr
  have hp1b : |p.1| * d ≤ 2 * ‖w‖ * ‖Z‖ := by
    calc
      _ = |p.1 * d| := by rw [abs_mul, abs_of_pos hd]
      _ = |w.re * Z.im - w.im * Z.re| := congrArg abs hp1
      _ ≤ _ := real_cross_numerator_bound w Z
  have hp2b : |p.2| * d ≤ 2 * ‖b‖ * ‖Z‖ := by
    calc
      _ = |p.2 * d| := by rw [abs_mul, abs_of_pos hd]
      _ = |b.im * Z.re - b.re * Z.im| := congrArg abs hp2
      _ = |b.re * Z.im - b.im * Z.re| := abs_sub_comm _ _
      _ ≤ _ := real_cross_numerator_bound b Z
  have hprod : (|p.1| + |p.2|) * d ≤ 4 * a * B ^ 2 * ‖Z‖ := by
    calc
      _ = |p.1| * d + |p.2| * d := by ring
      _ ≤ 2 * ‖w‖ * ‖Z‖ + 2 * ‖b‖ * ‖Z‖ := add_le_add hp1b hp2b
      _ ≤ 2 * (a * B ^ 2) * ‖Z‖ + 2 * (a * B ^ 2) * ‖Z‖ := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num))
          (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num))
          (norm_nonneg _))
      _ = _ := by ring
  calc
    _ ≤ (4 * a * B ^ 2 * ‖Z‖) / d := (le_div_iff₀ hd).2 hprod
    _ ≤ (4 * a * B ^ 2 * ‖Z‖) / (a ^ 2 * B ^ 4 / 256) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdet
    _ = _ := by field_simp [ha.ne', hB.ne']; ring

/-- The actual coupled compatibility equation quantitatively controls its
two real increments. The baseline obstruction contains the full outer source
and the real fixed-inverse inner jet; its norm is not replaced by a proxy. -/
theorem actual_Hartree_moment_locked_coupled_inverse_bound_of_budget
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
      (1 + (D + 1) * G * B ^ 2) Msrc ≤ B ^ 2 / 16)
    (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume (L / a) B) (db dw : ℝ)
    (hcancel : actualMomentLockedCoupledCompatibility K L c
      (lt_trans (by norm_num : (0 : ℝ) < 2) hL) a (L / a) B Fp Fm hp hm F db dw = 0) :
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    |db| + |dw| ≤ 1024 / (a * B ^ 2) *
      ‖actualMomentLockedIntervalObstruction K (L / a) B F J.1 J.2‖ := by
  let hLp : 0 < L := lt_trans (by norm_num : (0 : ℝ) < 2) hL
  let cols := actualMomentLockedCoupledColumns K L c hLp a (L / a) B
  let A := originKummerReferenceIntegral K B
  let E := actualMomentLockedFullColumnBudget L c hLp a B ((D + 1) * G)
    (1 + (D + 1) * G * B ^ 2) Msrc
  have hColumns := actual_Hartree_moment_locked_full_column_bounds
    Msrc hMsrc hClose K D G hD hG hB hBR hcoeff hbound L c a hL ha hLB
  dsimp only at hColumns
  have hCols : ‖cols.1 / (a : ℂ) + Complex.I * A / 2‖ ≤ E ∧
      ‖cols.2 / (a : ℂ) - A‖ ≤ E := hColumns
  have hE : E ≤ B ^ 2 / 16 := hBudget
  have hDet := actual_Hartree_moment_locked_coupled_determinant_lower_bound_of_budget
    Msrc hMsrc hClose K D G hD hG hB hBR hcoeff hbound hsmallB
    L c a hL ha hLB hBudget
  have hErr := origin_kummer_reference_integral_error_bound K D G hD hG
    hB.le hBR.le hcoeff hbound
  have hSmallErr : ((D + 1) * G + 1 / 4) * B ^ 4 / 4 ≤ B ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_right hsmallB (sq_nonneg B)
    nlinarith only [h]
  have hApprox := hErr.trans hSmallErr
  change ‖A - ((B ^ 2 / 2 : ℝ) : ℂ)‖ ≤ B ^ 2 / 4 at hApprox
  have hA : ‖A‖ ≤ 3 * B ^ 2 / 4 := by
    have ht := norm_add_le (A - ((B ^ 2 / 2 : ℝ) : ℂ)) ((B ^ 2 / 2 : ℝ) : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ B ^ 2 / 2)] at ht
    linarith only [ht, hApprox]
  have hRef : ‖Complex.I * A / 2‖ = ‖A‖ / 2 := by norm_num [norm_div, norm_mul]
  have hbNorm : ‖cols.1 / (a : ℂ)‖ ≤ B ^ 2 := by
    have ht := norm_sub_le (cols.1 / (a : ℂ) + Complex.I * A / 2) (Complex.I * A / 2)
    rw [add_sub_cancel_right, hRef] at ht
    linarith only [ht, hCols.1, hE, hA, sq_nonneg B]
  have hwNorm : ‖cols.2 / (a : ℂ)‖ ≤ B ^ 2 := by
    have ht := norm_add_le (cols.2 / (a : ℂ) - A) A
    rw [sub_add_cancel] at ht
    linarith only [ht, hCols.2, hE, hA, sq_nonneg B]
  have hbRaw : ‖cols.1‖ ≤ a * B ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at hbNorm
    exact ((div_le_iff₀ ha).1 hbNorm).trans_eq (by ring)
  have hwRaw : ‖cols.2‖ ≤ a * B ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at hwNorm
    exact ((div_le_iff₀ ha).1 hwNorm).trans_eq (by ring)
  have hK := origin_kummer_annulus_bound K (L / a) B G (div_pos hLp ha) hBR hG hbound
  have hAff := actual_Hartree_moment_locked_full_coupled_response
    K (div_pos hLp ha) hLB hK L c hLp a ha Fp Fm hp hm F hF db dw
  dsimp only at hAff ⊢
  exact actual_columns_cancellation_bound a B ha hB cols.1 cols.2 _ (db, dw)
    hbRaw hwRaw hDet.1 (hAff.symm.trans hcancel)

/-- A real physical parameter region makes the preceding inverse estimate
uniform. Its column budget is derived from the same fixed Fredholm response
growth as the accepted determinant theorem; no budget is left as a premise. -/
theorem actual_Hartree_moment_locked_coupled_inverse_bound_region
    {mu theta R B : ℝ} (K : OriginKummerPair mu theta R)
    (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B) (hBR : B < R)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon : ℝ, 3 ≤ L0 ∧ 0 < epsilon ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → |c| ≤ 1 → a * |c| ≤ epsilon →
        ∀ (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
          (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
          (F : ℝ → ℂ) (hF : IntervalIntegrable F volume (L / a) B) (db dw : ℝ),
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F db dw = 0 →
          let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
          |db| + |dw| ≤ 1024 / (a * B ^ 2) *
            ‖actualMomentLockedIntervalObstruction K (L / a) B F J.1 J.2‖ := by
  obtain ⟨Msrc, hMsrc, hClose⟩ := actual_Hartree_moment_locked_speed_profiles_uniform_close
  obtain ⟨Cg, hCg, hGrowth⟩ := actual_Hartree_moment_locked_response_moment_growth
  let H : ℝ := (D + 1) * G
  let C0 : ℝ := 1 + H * B ^ 2
  let Dg : ℝ := 2 * Cg
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hDg : 0 ≤ Dg := by dsimp [Dg]; positivity
  let K0 : ℝ := C0 * (1 + 2 * B ^ 2 + Dg) + 4 * H * Dg
  let L0 : ℝ := 3 + 32 * K0 / B ^ 2 + 1 / B
  let epsilon : ℝ := B ^ 2 / (32 * (C0 * Msrc * B ^ 3 + 1))
  have hRegion := actual_coupled_explicit_small_parameter_region
    C0 H Msrc Dg B hC0 hH hMsrc.le hDg hB
  have hL0 : 3 ≤ L0 := hRegion.1
  refine ⟨L0, epsilon, hL0, hRegion.2.1, ?_⟩
  intro L c a hLp hLarge ha hc hSmall Fp Fm hp hm F hF db dw hcancel
  have hLone : 1 ≤ L := by linarith
  have hLtwo : 2 < L := by linarith
  have hapos : 0 < a := (pow_pos hLp 3).trans_le ha
  have hData := hGrowth L c hLone hc
  dsimp only at hData
  have hMoment : actualMomentLockedResponseMomentSum L c hLp ≤ Dg * L ^ 4 := by
    calc
      _ ≤ Cg * L ^ 4 + Cg * L ^ 4 := add_le_add hData.2.2.2.1 hData.2.2.2.2
      _ = _ := by dsimp [Dg]; ring
  have hCharge : actualMomentLockedResponseChargeSum L c ≤ Dg * L ^ 4 := by
    calc
      _ ≤ Cg * L ^ 4 + Cg * L ^ 4 := add_le_add hData.2.1.1 hData.2.1.2
      _ = _ := by dsimp [Dg]; ring
  have hSmallBudget := hRegion.2.2 L a c
    (actualMomentLockedResponseMomentSum L c hLp) (actualMomentLockedResponseChargeSum L c)
    hLarge ha hSmall hMoment hCharge
  have hBudget : actualMomentLockedFullColumnBudget L c hLp a B H C0 Msrc ≤ B ^ 2 / 16 := by
    simpa only [actualMomentLockedFullColumnBudget,
      actualMomentLockedCoupledTraceBudget, add_assoc] using hSmallBudget.2.2
  exact actual_Hartree_moment_locked_coupled_inverse_bound_of_budget
    Msrc hMsrc hClose K D G hD hG hB hBR hcoeff hbound hsmallB
    L c a hLtwo hapos hSmallBudget.2.1 hBudget Fp Fm hp hm F hF db dw hcancel

end HBL.TypeIIDynamicSelection
