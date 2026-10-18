import HBL.MonopoleFredholmSolution
import HBL.WeightedHartreePointwiseBound

/-!
Pointwise Green representative and tail bootstrap for the first monopole
Fredholm solution.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- Total weighted source after the Fredholm unknown has been found. -/
def monopoleTotalDatum : RealL2 halfLineMeasure :=
  weightedPotentialOperator
      (monopoleFredholmSolution : RealL2 halfLineMeasure) +
    weightedMonopoleDatumL2 monopoleAffineSlope

/-- Canonical continuous unweighted Green representative of the normalized
remainder. -/
def monopoleRemainder (r : ℝ) : ℝ :=
  weightedGreenPrimitive monopoleTotalDatum r

theorem monopoleRemainder_continuous : Continuous monopoleRemainder := by
  exact weightedGreenPrimitive_continuous monopoleTotalDatum

theorem monopoleFredholmSolution_ae_remainder :
    ((monopoleFredholmSolution : RealL2 halfLineMeasure) : ℝ → ℝ)
      =ᵐ[halfLineMeasure]
        fun r => weightedGreenDecay r * monopoleRemainder r := by
  rw [monopoleFredholmSolution_eq_green]
  have h := weightedFreeGreenOperator_ae_pointwise monopoleTotalDatum
  filter_upwards [h] with r hr
  simpa [monopoleTotalDatum, monopoleRemainder,
    weightedFreeGreenPointwise] using hr

/-- An explicit finite bound for every positive-radius Green primitive. -/
def weightedGreenPrimitiveBound (f : RealL2 halfLineMeasure) : ℝ :=
  ∫ rho : ℝ, ‖weightedGreenOutputMajorant rho * f rho‖
    ∂halfLineMeasure

theorem weightedGreenPrimitiveBound_nonneg
    (f : RealL2 halfLineMeasure) :
    0 ≤ weightedGreenPrimitiveBound f :=
  integral_nonneg fun _ => norm_nonneg _

theorem weightedGreenOutputMajorant_mul_integrable
    (f : RealL2 halfLineMeasure) :
    Integrable (fun rho : ℝ =>
      weightedGreenOutputMajorant rho * f rho) halfLineMeasure :=
  weightedGreenOutputMajorant_memLp_two.integrable_mul (Lp.memLp f)

theorem weightedGreenPrimitive_abs_le_bound
    (f : RealL2 halfLineMeasure) {r : ℝ} (hr : 0 < r) :
    |weightedGreenPrimitive f r| ≤ weightedGreenPrimitiveBound f := by
  unfold weightedGreenPrimitive weightedGreenPrimitiveBound
  calc
    |∫ rho : ℝ, min r rho * (weightedGreenDecay rho * f rho)
        ∂halfLineMeasure| ≤
        ∫ rho : ℝ,
          ‖min r rho * (weightedGreenDecay rho * f rho)‖
          ∂halfLineMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ rho : ℝ,
          ‖weightedGreenOutputMajorant rho * f rho‖
          ∂halfLineMeasure := by
      apply integral_mono_ae
      · exact (weightedGreenPrimitive_integrable_kernel f r).norm
      · exact (weightedGreenOutputMajorant_mul_integrable f).norm
      · filter_upwards [ae_restrict_mem measurableSet_Ioi]
          with rho hρ
        have hmin : |min r rho| ≤ |rho| := by
          rw [abs_of_pos (lt_min hr hρ), abs_of_pos hρ]
          exact min_le_right _ _
        unfold weightedGreenOutputMajorant
        simpa only [Real.norm_eq_abs, abs_mul, abs_abs, mul_assoc] using
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hmin
              (abs_nonneg (weightedGreenDecay rho)))
            (abs_nonneg (f rho))

theorem monopoleRemainder_abs_le
    {r : ℝ} (hr : 0 < r) :
    |monopoleRemainder r| ≤
      weightedGreenPrimitiveBound monopoleTotalDatum :=
  weightedGreenPrimitive_abs_le_bound monopoleTotalDatum hr

/-- Original-variable source in the remainder equation `-h'' = S`. -/
def monopoleRemainderSource (r : ℝ) : ℝ :=
  monopoleCorrectedSource monopoleAffineSlope r +
    9 * weightedGreenDecay r ^ 2 * monopoleRemainder r +
    nonlocalApply monopoleRemainder r

theorem monopoleRemainder_weighted_memLp_two :
    MemLp (fun r => weightedGreenDecay r * monopoleRemainder r) 2
      halfLineMeasure := by
  exact (memLp_congr_ae monopoleFredholmSolution_ae_remainder).mp
    (Lp.memLp (monopoleFredholmSolution : RealL2 halfLineMeasure))

theorem monopoleRemainder_weighted_toLp :
    monopoleRemainder_weighted_memLp_two.toLp
        (fun r => weightedGreenDecay r * monopoleRemainder r) =
      (monopoleFredholmSolution : RealL2 halfLineMeasure) := by
  apply Lp.ext
  exact monopoleRemainder_weighted_memLp_two.coeFn_toLp.trans
    monopoleFredholmSolution_ae_remainder.symm

theorem weightedHartreePointwise_solution_conjugation (r : ℝ) :
    weightedHartreePointwise
        (monopoleFredholmSolution : RealL2 halfLineMeasure) r =
      (1 + r ^ 2) * nonlocalApply monopoleRemainder r := by
  rw [← monopoleRemainder_weighted_toLp]
  exact weightedHartreePointwise_conjugation monopoleRemainder
    monopoleRemainder_weighted_memLp_two r

theorem nonlocalApply_monopoleRemainder_ae_norm_le :
    ∀ᵐ r ∂halfLineMeasure,
      |nonlocalApply monopoleRemainder r| ≤
        Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
          ‖(monopoleFredholmSolution : RealL2 halfLineMeasure)‖ := by
  have h := nonlocalApply_ae_norm_le_of_weighted_memLp
    monopoleRemainder monopoleRemainder_weighted_memLp_two
  simpa only [monopoleRemainder_weighted_toLp] using h

/-- Multiplying the total conjugated datum by the Green weight gives
exactly the source in the original half-line remainder equation. -/
theorem weightedGreen_totalDatum_ae_source :
    (fun r : ℝ => weightedGreenDecay r * monopoleTotalDatum r)
      =ᵐ[halfLineMeasure] monopoleRemainderSource := by
  let x : RealL2 halfLineMeasure :=
    (monopoleFredholmSolution : RealL2 halfLineMeasure)
  have htotal : monopoleTotalDatum =
      ((9 : ℝ) • x + weightedHartreeOperator x) +
        weightedMonopoleDatumL2 monopoleAffineSlope := by
    rfl
  rw [htotal]
  filter_upwards [
    Lp.coeFn_add ((9 : ℝ) • x + weightedHartreeOperator x)
      (weightedMonopoleDatumL2 monopoleAffineSlope),
    Lp.coeFn_add ((9 : ℝ) • x) (weightedHartreeOperator x),
    Lp.coeFn_smul (9 : ℝ) x,
    weightedHartreeOperator_ae_pointwise x,
    monopoleFredholmSolution_ae_remainder,
    weightedMonopoleDatumL2_ae monopoleAffineSlope] with r
      htotalPoint hpotPoint hlocalPoint hhartree hx hdatum
  simp only [Pi.add_apply] at htotalPoint hpotPoint
  simp only [Pi.smul_apply, smul_eq_mul] at hlocalPoint
  rw [htotalPoint, hpotPoint, hlocalPoint, hhartree, hx, hdatum]
  rw [weightedHartreePointwise_solution_conjugation]
  unfold monopoleRemainderSource weightedMonopoleDatum
    weightedGreenDecay
  field_simp [show 1 + r ^ 2 ≠ 0 by positivity]
  ring

theorem monopoleRemainderSource_integrable :
    Integrable monopoleRemainderSource halfLineMeasure := by
  exact (weightedGreen_source_integrable monopoleTotalDatum).congr
    weightedGreen_totalDatum_ae_source

/-- The continuous Fredholm representative is the ordinary half-line
Green integral of its original-variable source. -/
theorem monopoleRemainder_eq_halfLineMinGreen (r : ℝ) :
    monopoleRemainder r = halfLineMinGreen monopoleRemainderSource r := by
  unfold monopoleRemainder weightedGreenPrimitive halfLineMinGreen
  apply integral_congr_ae
  filter_upwards [weightedGreen_totalDatum_ae_source] with rho hsource
  rw [hsource]

end HBL.Modulation.Monopole
