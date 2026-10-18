import HBL.MonopoleFredholmTail

/-!
Quantitative decay of the source in the first monopole Fredholm equation.
The estimates here are deliberately stated almost everywhere, exactly at
the regularity supplied by the Hilbert--Schmidt realization of the Hartree
operator.
-/

noncomputable section

open Set MeasureTheory Filter

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- Exact pointwise decomposition of the corrected source into the
logarithmic cancellation, local weighted terms, and the two Hartree terms. -/
theorem monopoleCorrectedSource_decomposition (ell r : ℝ) :
    monopoleCorrectedSource ell r =
      weightedGreenDecay r * weightedMonopoleCancellation r +
      9 * weightedGreenDecay r ^ 2 * monopoleLogModel r +
      ell * weightedGreenDecay r * weightedAffineCurvature r +
      9 * ell * weightedGreenDecay r ^ 2 * model r +
      nonlocalApply monopoleLogModel r +
      ell * nonlocalApply model r := by
  unfold monopoleCorrectedSource hPlusApply potential
    weightedMonopoleCancellation weightedAffineCurvature
    weightedGreenDecay
  field_simp [show 1 + r ^ 2 ≠ 0 by positivity]
  ring

theorem bubble_nonneg (r : ℝ) : 0 ≤ bubble r := by
  unfold bubble
  positivity

theorem bubble_le_one (r : ℝ) : bubble r ≤ 1 := by
  have ha := weightedGreenDecay_le_one r
  rw [show weightedGreenDecay r = bubble r ^ 2 by
    exact (bubble_sq r).symm] at ha
  nlinarith [bubble_nonneg r]

theorem radius_mul_bubble_le_one {r : ℝ} (hr : 0 ≤ r) :
    r * bubble r ≤ 1 := by
  unfold bubble
  have hs : 0 < Real.sqrt (1 + r ^ 2) := by positivity
  change r / Real.sqrt (1 + r ^ 2) ≤ 1
  rw [div_le_one hs]
  rw [Real.le_sqrt hr (by positivity)]
  nlinarith [sq_nonneg r]

theorem weightedGreenDecay_sq_le_bubble_cube (r : ℝ) :
    weightedGreenDecay r ^ 2 ≤ bubble r ^ 3 := by
  rw [show weightedGreenDecay r = bubble r ^ 2 by
    exact (bubble_sq r).symm]
  have hb0 := bubble_nonneg r
  have hb1 := bubble_le_one r
  calc
    (bubble r ^ 2) ^ 2 = bubble r ^ 3 * bubble r := by ring
    _ ≤ bubble r ^ 3 * 1 :=
      mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = bubble r ^ 3 := by ring

theorem radius_mul_weightedGreenDecay_sq_le_bubble_cube
    {r : ℝ} (hr : 0 ≤ r) :
    r * weightedGreenDecay r ^ 2 ≤ bubble r ^ 3 := by
  rw [show weightedGreenDecay r = bubble r ^ 2 by
    exact (bubble_sq r).symm]
  calc
    r * (bubble r ^ 2) ^ 2 =
        bubble r ^ 3 * (r * bubble r) := by ring
    _ ≤ bubble r ^ 3 * 1 :=
      mul_le_mul_of_nonneg_left (radius_mul_bubble_le_one hr)
        (pow_nonneg (bubble_nonneg r) _)
    _ = bubble r ^ 3 := by ring

private theorem abs_add_six_le (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤
      |a| + |b| + |c| + |d| + |e| + |f| := by
  calc
    |a + b + c + d + e + f| ≤ |a + b + c + d + e| + |f| :=
      abs_add_le _ _
    _ ≤ (|a + b + c + d| + |e|) + |f| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ((|a + b + c| + |d|) + |e|) + |f| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ (((|a + b| + |c|) + |d|) + |e|) + |f| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ((((|a| + |b|) + |c|) + |d|) + |e|) + |f| := by
      gcongr
      exact abs_add_le _ _
    _ = |a| + |b| + |c| + |d| + |e| + |f| := by ring

/-- A concrete coefficient for the corrected-source `W³` bound. -/
def monopoleCorrectedDecayConstant : ℝ :=
  2 + 9 + 9 * |monopoleAffineSlope| +
    Real.sqrt (288 * Real.pi) *
      (‖weightedLogModelL2‖ +
        |monopoleAffineSlope| * ‖weightedAffineModelL2‖)

theorem monopoleCorrectedDecayConstant_nonneg :
    0 ≤ monopoleCorrectedDecayConstant := by
  unfold monopoleCorrectedDecayConstant
  positivity

theorem nonlocalApply_monopoleLogModel_ae_norm_le :
    ∀ᵐ r ∂halfLineMeasure,
      |nonlocalApply monopoleLogModel r| ≤
        Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
          ‖weightedLogModelL2‖ := by
  have h := nonlocalApply_ae_norm_le_of_weighted_memLp
    monopoleLogModel weightedLogModel_memLp_two
  change ∀ᵐ r ∂halfLineMeasure,
    |nonlocalApply monopoleLogModel r| ≤
      Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
        ‖weightedLogModel_memLp_two.toLp
          (fun rho => weightedGreenDecay rho * monopoleLogModel rho)‖
  exact h

theorem nonlocalApply_model_ae_norm_le :
    ∀ᵐ r ∂halfLineMeasure,
      |nonlocalApply model r| ≤
        Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
          ‖weightedAffineModelL2‖ := by
  have h := nonlocalApply_ae_norm_le_of_weighted_memLp
    model weightedAffineModel_memLp_two
  change ∀ᵐ r ∂halfLineMeasure,
    |nonlocalApply model r| ≤
      Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
        ‖weightedAffineModel_memLp_two.toLp
          (fun rho => weightedGreenDecay rho * model rho)‖
  exact h

/-- Far from the cutoff region, the corrected Fredholm source has the
sharp `W³` decay required by the Green tail argument. -/
theorem monopoleCorrectedSource_ae_norm_le :
    ∀ᵐ r ∂halfLineMeasure,
      2 < r →
        |monopoleCorrectedSource monopoleAffineSlope r| ≤
          monopoleCorrectedDecayConstant * bubble r ^ 3 := by
  filter_upwards [nonlocalApply_monopoleLogModel_ae_norm_le,
    nonlocalApply_model_ae_norm_le] with r hNlog hNmodel
  intro hr
  have hr0 : 0 ≤ r := by linarith
  have ha0 : 0 ≤ weightedGreenDecay r := weightedGreenDecay_nonneg r
  have hb30 : 0 ≤ bubble r ^ 3 := pow_nonneg (bubble_nonneg r) _
  have hcancel0 :
      |weightedGreenDecay r * weightedMonopoleCancellation r| ≤
        2 * bubble r ^ 3 := by
    rw [abs_mul, abs_of_nonneg ha0]
    calc
      weightedGreenDecay r * |weightedMonopoleCancellation r| ≤
          weightedGreenDecay r * (2 * weightedGreenDecay r) :=
        mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using
            weightedMonopoleCancellation_norm_far_le r hr) ha0
      _ = 2 * weightedGreenDecay r ^ 2 := by ring
      _ ≤ 2 * bubble r ^ 3 := by
        gcongr
        exact weightedGreenDecay_sq_le_bubble_cube r
  have hlogModel : |monopoleLogModel r| ≤ r := by
    calc
      |monopoleLogModel r| ≤ model r :=
        monopoleLogModel_abs_le_model r
      _ = r := model_eq_id_of_two_le r hr.le
  have hlog0 :
      |9 * weightedGreenDecay r ^ 2 * monopoleLogModel r| ≤
        9 * bubble r ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
      abs_of_nonneg (sq_nonneg _)]
    calc
      9 * weightedGreenDecay r ^ 2 * |monopoleLogModel r| ≤
          9 * weightedGreenDecay r ^ 2 * r :=
        mul_le_mul_of_nonneg_left hlogModel (by positivity)
      _ = 9 * (r * weightedGreenDecay r ^ 2) := by ring
      _ ≤ 9 * bubble r ^ 3 := by
        gcongr
        exact radius_mul_weightedGreenDecay_sq_le_bubble_cube hr0
  have hcurv0 :
      |monopoleAffineSlope * weightedGreenDecay r *
          weightedAffineCurvature r| = 0 := by
    rw [weightedAffineCurvature_zero_of_two_lt r hr, mul_zero, abs_zero]
  have haff0 :
      |9 * monopoleAffineSlope * weightedGreenDecay r ^ 2 * model r| ≤
        9 * |monopoleAffineSlope| * bubble r ^ 3 := by
    rw [model_eq_id_of_two_le r hr.le]
    simp only [abs_mul, abs_of_nonneg hr0,
      abs_of_nonneg (sq_nonneg (weightedGreenDecay r))]
    norm_num
    calc
      9 * |monopoleAffineSlope| * weightedGreenDecay r ^ 2 * r =
          (9 * |monopoleAffineSlope|) *
            (r * weightedGreenDecay r ^ 2) := by ring
      _ ≤ (9 * |monopoleAffineSlope|) * bubble r ^ 3 :=
        mul_le_mul_of_nonneg_left
          (radius_mul_weightedGreenDecay_sq_le_bubble_cube hr0)
          (by positivity)
  have hNaff :
      |monopoleAffineSlope * nonlocalApply model r| ≤
        |monopoleAffineSlope| *
          (Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
            ‖weightedAffineModelL2‖) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hNmodel (abs_nonneg _)
  calc
    |monopoleCorrectedSource monopoleAffineSlope r| =
      |weightedGreenDecay r * weightedMonopoleCancellation r +
        9 * weightedGreenDecay r ^ 2 * monopoleLogModel r +
        monopoleAffineSlope * weightedGreenDecay r *
          weightedAffineCurvature r +
        9 * monopoleAffineSlope * weightedGreenDecay r ^ 2 * model r +
        nonlocalApply monopoleLogModel r +
        monopoleAffineSlope * nonlocalApply model r| := by
      rw [monopoleCorrectedSource_decomposition]
    _ ≤
        |weightedGreenDecay r * weightedMonopoleCancellation r| +
        |9 * weightedGreenDecay r ^ 2 * monopoleLogModel r| +
        |monopoleAffineSlope * weightedGreenDecay r *
          weightedAffineCurvature r| +
        |9 * monopoleAffineSlope * weightedGreenDecay r ^ 2 * model r| +
        |nonlocalApply monopoleLogModel r| +
        |monopoleAffineSlope * nonlocalApply model r| :=
      abs_add_six_le _ _ _ _ _ _
    _ ≤ 2 * bubble r ^ 3 + 9 * bubble r ^ 3 + 0 +
        9 * |monopoleAffineSlope| * bubble r ^ 3 +
        (Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
          ‖weightedLogModelL2‖) +
        |monopoleAffineSlope| *
          (Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
            ‖weightedAffineModelL2‖) := by
      rw [hcurv0]
      linarith [hcancel0, hlog0, haff0, hNlog, hNaff]
    _ ≤ monopoleCorrectedDecayConstant * bubble r ^ 3 := by
      unfold monopoleCorrectedDecayConstant
      ring_nf
      exact le_rfl

/-- Concrete coefficient for the full remainder source. -/
def monopoleSourceDecayConstant : ℝ :=
  monopoleCorrectedDecayConstant +
    9 * weightedGreenPrimitiveBound monopoleTotalDatum +
    Real.sqrt (288 * Real.pi) *
      ‖(monopoleFredholmSolution : RealL2 halfLineMeasure)‖

theorem monopoleSourceDecayConstant_nonneg :
    0 ≤ monopoleSourceDecayConstant := by
  unfold monopoleSourceDecayConstant
  exact add_nonneg
    (add_nonneg monopoleCorrectedDecayConstant_nonneg
      (mul_nonneg (by norm_num)
        (weightedGreenPrimitiveBound_nonneg monopoleTotalDatum)))
    (mul_nonneg (Real.sqrt_nonneg _)
      (norm_nonneg (monopoleFredholmSolution : RealL2 halfLineMeasure)))

/-- The complete source `-h''` is `O(W³)` almost everywhere. -/
theorem monopoleRemainderSource_ae_norm_le :
    ∀ᵐ r ∂halfLineMeasure,
      2 < r →
        |monopoleRemainderSource r| ≤
          monopoleSourceDecayConstant * bubble r ^ 3 := by
  filter_upwards [monopoleCorrectedSource_ae_norm_le,
    nonlocalApply_monopoleRemainder_ae_norm_le] with r hcorr hN
  intro hr
  have hr0 : 0 < r := by linarith
  have ha0 : 0 ≤ weightedGreenDecay r := weightedGreenDecay_nonneg r
  have hb30 : 0 ≤ bubble r ^ 3 := pow_nonneg (bubble_nonneg r) _
  have hlocal :
      |9 * weightedGreenDecay r ^ 2 * monopoleRemainder r| ≤
        9 * weightedGreenPrimitiveBound monopoleTotalDatum *
          bubble r ^ 3 := by
    rw [abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
      abs_of_nonneg (sq_nonneg _)]
    calc
      9 * weightedGreenDecay r ^ 2 * |monopoleRemainder r| ≤
          9 * weightedGreenDecay r ^ 2 *
            weightedGreenPrimitiveBound monopoleTotalDatum :=
        mul_le_mul_of_nonneg_left (monopoleRemainder_abs_le hr0)
          (by positivity)
      _ = (9 * weightedGreenPrimitiveBound monopoleTotalDatum) *
          weightedGreenDecay r ^ 2 := by ring
      _ ≤ (9 * weightedGreenPrimitiveBound monopoleTotalDatum) *
          bubble r ^ 3 :=
        mul_le_mul_of_nonneg_left
          (weightedGreenDecay_sq_le_bubble_cube r)
          (mul_nonneg (by norm_num)
            (weightedGreenPrimitiveBound_nonneg monopoleTotalDatum))
      _ = 9 * weightedGreenPrimitiveBound monopoleTotalDatum *
          bubble r ^ 3 := by ring
  have hN' :
      |nonlocalApply monopoleRemainder r| ≤
        (Real.sqrt (288 * Real.pi) *
          ‖(monopoleFredholmSolution : RealL2 halfLineMeasure)‖) *
            bubble r ^ 3 := by
    calc
      |nonlocalApply monopoleRemainder r| ≤
          Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
            ‖(monopoleFredholmSolution : RealL2 halfLineMeasure)‖ := hN
      _ = (Real.sqrt (288 * Real.pi) *
          ‖(monopoleFredholmSolution : RealL2 halfLineMeasure)‖) *
            bubble r ^ 3 := by ring
  unfold monopoleRemainderSource
  calc
    |monopoleCorrectedSource monopoleAffineSlope r +
        9 * weightedGreenDecay r ^ 2 * monopoleRemainder r +
        nonlocalApply monopoleRemainder r| ≤
        |monopoleCorrectedSource monopoleAffineSlope r| +
          |9 * weightedGreenDecay r ^ 2 * monopoleRemainder r| +
          |nonlocalApply monopoleRemainder r| := by
      calc
        |monopoleCorrectedSource monopoleAffineSlope r +
            9 * weightedGreenDecay r ^ 2 * monopoleRemainder r +
            nonlocalApply monopoleRemainder r| ≤
            |monopoleCorrectedSource monopoleAffineSlope r +
              9 * weightedGreenDecay r ^ 2 * monopoleRemainder r| +
              |nonlocalApply monopoleRemainder r| := abs_add_le _ _
        _ ≤ (|monopoleCorrectedSource monopoleAffineSlope r| +
              |9 * weightedGreenDecay r ^ 2 * monopoleRemainder r|) +
              |nonlocalApply monopoleRemainder r| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ monopoleCorrectedDecayConstant * bubble r ^ 3 +
          (9 * weightedGreenPrimitiveBound monopoleTotalDatum) *
            bubble r ^ 3 +
          (Real.sqrt (288 * Real.pi) *
            ‖(monopoleFredholmSolution : RealL2 halfLineMeasure)‖) *
              bubble r ^ 3 := by
      linarith [hcorr hr, hlocal, hN']
    _ = monopoleSourceDecayConstant * bubble r ^ 3 := by
      unfold monopoleSourceDecayConstant
      ring

end HBL.Modulation.Monopole
