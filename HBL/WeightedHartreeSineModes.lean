import HBL.AngularHartreeSineAction
import HBL.WeightedHartreePointwiseContinuous

/-!
Explicit sine modes of the actual weighted radial Hartree kernel.  Their L2
membership and every nonnegative-radius row integral are justified before
the pointwise action is transferred to the existing kernel operator.
No completeness of these modes, full spectral classification, or additional
angular change-of-space isometry is asserted.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole
open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- Concrete radial pullback of the angular sine mode, including the correct
single bubble factor for the L2 radial measure dr. -/
def weightedHartreeSineMode (n : ℕ) (r : ℝ) : ℝ :=
  bubble r * Real.sin (2 * (n : ℝ) * Real.arctan r)

private theorem weightedHartreeSineMode_continuous (n : ℕ) :
    Continuous (weightedHartreeSineMode n) := by
  unfold weightedHartreeSineMode
  exact bubble_contDiff_infty.continuous.mul
    (Real.continuous_sin.comp (continuous_const.mul Real.continuous_arctan))

/-- Actual square integrability, derived from sin squared <= 1 and the
already integrable squared bubble. -/
theorem weightedHartreeSineMode_memLp (n : ℕ) :
    MemLp (weightedHartreeSineMode n) 2 halfLineMeasure := by
  have hm := (weightedHartreeSineMode_continuous n).aestronglyMeasurable
    (μ := halfLineMeasure)
  apply (memLp_two_iff_integrable_sq hm).2
  have hb : Integrable birmanSquareWeight halfLineMeasure :=
    birmanSquareWeight_integrable.integrableOn
  apply hb.mono' ((weightedHartreeSineMode_continuous n).pow 2).aestronglyMeasurable
  filter_upwards with r
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold weightedHartreeSineMode birmanSquareWeight
  rw [Pi.pow_apply, mul_pow]
  exact (mul_le_mul_of_nonneg_left (Real.sin_sq_le_one _) (sq_nonneg (bubble r))).trans_eq
    (mul_one _)

/-- The mode in the already constructed real half-line L2 space. -/
def weightedHartreeSineModeL2 (n : ℕ) : RealL2 halfLineMeasure :=
  (weightedHartreeSineMode_memLp n).toLp (weightedHartreeSineMode n)

theorem weightedHartreeSineModeL2_ae (n : ℕ) :
    (weightedHartreeSineModeL2 n : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedHartreeSineMode n :=
  (weightedHartreeSineMode_memLp n).coeFn_toLp

/-- Every actual row-times-mode integral is absolutely convergent, including
the radius-zero row; no integrability hypothesis is supplied. -/
theorem weightedHartreeSineMode_row_integrable (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun rho => weightedHartreeKernel r rho * weightedHartreeSineMode n rho)
      halfLineMeasure :=
  (weightedHartreeKernel_row_memLp hr).integrable_mul (weightedHartreeSineMode_memLp n)

/-- Exact pointwise action of the actual weighted logarithmic kernel. -/
theorem weightedHartreeSineMode_integral (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 ≤ r) :
    (∫ rho : ℝ, weightedHartreeKernel r rho * weightedHartreeSineMode n rho
      ∂halfLineMeasure) = (12 / (n : ℝ)) * weightedHartreeSineMode n r := by
  have htheta : Real.arctan r ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨Real.arctan_nonneg.mpr hr, (Real.arctan_lt_pi_div_two r).le⟩
  let g : ℝ → ℝ := fun theta =>
    angularHartreeLog (Real.arctan r) theta * Real.sin (2 * (n : ℝ) * theta)
  let C : ℝ := (24 / Real.pi) * bubble r
  calc
    (∫ rho : ℝ, weightedHartreeKernel r rho * weightedHartreeSineMode n rho
        ∂halfLineMeasure) =
        ∫ rho in Ioi (0 : ℝ), C * (bubble rho ^ 2 * g (Real.arctan rho)) := by
      apply integral_congr_ae
      filter_upwards [(Measure.ae_ne volume r).filter_mono ae_restrict_le] with rho hne
      rw [weightedHartreeKernel_eq_angular r rho hne.symm]
      dsimp only [C, g, weightedHartreeSineMode]
      ring
    _ = C * ∫ rho in Ioi (0 : ℝ), bubble rho ^ 2 * g (Real.arctan rho) := by
      rw [integral_const_mul]
    _ = C * ∫ theta : ℝ in 0..Real.pi / 2, g theta := by
      rw [intervalIntegral_eq_integral_Ioi_arctan]
    _ = (12 / (n : ℝ)) * weightedHartreeSineMode n r := by
      rw [show (∫ theta : ℝ in 0..Real.pi / 2, g theta) =
        Real.pi / (2 * (n : ℝ)) * Real.sin (2 * (n : ℝ) * Real.arctan r) from
          integral_angularHartreeLog_mul_sin_half htheta n hn]
      dsimp only [C, weightedHartreeSineMode]
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
      field_simp [Real.pi_ne_zero, hn0]
      ring

/-- Genuine equality in the existing L2 kernel operator, obtained from its
proved almost-everywhere integral representation and the actual mode. -/
theorem weightedHartreeOperator_sineMode (n : ℕ) (hn : 0 < n) :
    weightedHartreeOperator (weightedHartreeSineModeL2 n) =
      (12 / (n : ℝ)) • weightedHartreeSineModeL2 n := by
  apply Lp.ext
  filter_upwards [weightedHartreeOperator_ae_pointwise (weightedHartreeSineModeL2 n),
    Lp.coeFn_smul (12 / (n : ℝ)) (weightedHartreeSineModeL2 n),
    weightedHartreeSineModeL2_ae n,
    ae_restrict_mem measurableSet_Ioi] with r hop hsmul hmode hr
  rw [hop, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hmode]
  calc
    weightedHartreePointwise (weightedHartreeSineModeL2 n) r =
        ∫ rho : ℝ, weightedHartreeKernel r rho * weightedHartreeSineMode n rho
          ∂halfLineMeasure := by
      apply integral_congr_ae
      filter_upwards [weightedHartreeSineModeL2_ae n] with rho hmode
      rw [hmode]
    _ = _ := weightedHartreeSineMode_integral n hn hr.le

end HBL.Modulation.Monopole
