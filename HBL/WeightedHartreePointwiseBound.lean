import HBL.WeightedHartreeSquareIdentity
import HBL.L2KernelPointwise

/-!
Pointwise decay of the weighted Hartree integral.

The exact square-kernel identity computes the `L²` norm of almost every
kernel row.  Cauchy--Schwarz then gives the `W(r)` decay needed in the
monopole tail bootstrap.
-/

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- Canonical pointwise integral associated with the weighted Hartree
kernel. -/
def weightedHartreePointwise
    (f : RealL2 halfLineMeasure) (r : ℝ) : ℝ :=
  ∫ rho : ℝ, weightedHartreeKernel r rho * f rho ∂halfLineMeasure

theorem weightedHartreeOperator_ae_pointwise
    (f : RealL2 halfLineMeasure) :
    (weightedHartreeOperator f : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedHartreePointwise f := by
  exact operator_toLp_ae_eq_integral
    weightedHartreeKernel weightedHartreeKernel_memLp_two f

/-- Exact pointwise conjugation for every radius; the input representative
may change on a null set without changing the integral. -/
theorem weightedHartreePointwise_conjugation
    (q : ℝ → ℝ)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2
      halfLineMeasure) (r : ℝ) :
    weightedHartreePointwise
        (hq.toLp (fun rho => weightedGreenDecay rho * q rho)) r =
      (1 + r ^ 2) * nonlocalApply q r := by
  have hqae := hq.coeFn_toLp
  unfold weightedHartreePointwise nonlocalApply
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hqae] with rho hρ
  rw [hρ]
  unfold weightedHartreeKernel hartreeKernel hartreeRadialLog
    weightedGreenDecay bubble
  have hsr : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hsρ : Real.sqrt (1 + rho ^ 2) ≠ 0 := by positivity
  have hsr2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hsρ2 : Real.sqrt (1 + rho ^ 2) ^ 2 = 1 + rho ^ 2 :=
    Real.sq_sqrt (by positivity)
  field_simp [hsr, hsρ]
  rw [hsr2, hsρ2]

theorem weightedZeroGreen_diag_le
    {r : ℝ} (hr : 0 < r) :
    weightedZeroGreen r r ≤
      (Real.pi / 2) * bubble r ^ 2 := by
  have htheta : Real.arctan r ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨(Real.arctan_pos.mpr hr).le,
      (Real.arctan_lt_pi_div_two r).le⟩
  have hD := angularZeroGreen_le_pi_div_two htheta htheta
  have hb2 : 0 ≤ bubble r ^ 2 := sq_nonneg _
  unfold weightedZeroGreen
  calc
    bubble r * bubble r *
        angularZeroGreen (Real.arctan r) (Real.arctan r) =
        bubble r ^ 2 *
          angularZeroGreen (Real.arctan r) (Real.arctan r) := by ring
    _ ≤ bubble r ^ 2 * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_left hD hb2
    _ = (Real.pi / 2) * bubble r ^ 2 := by ring

set_option maxHeartbeats 800000 in
/-- Almost every kernel row has the sharp decay furnished by the exact
Hartree square identity. -/
theorem weightedHartreePointwise_ae_norm_le
    (f : RealL2 halfLineMeasure) :
    ∀ᵐ r ∂halfLineMeasure,
      |weightedHartreePointwise f r| ≤
        Real.sqrt (288 * Real.pi) * bubble r * ‖f‖ := by
  have hrows := weightedHartreeKernel_sq_integrable.prod_right_ae
  filter_upwards [hrows, ae_restrict_mem measurableSet_Ioi]
      with r hrowSq hr
  have hrowMeas : AEStronglyMeasurable
      (fun rho : ℝ => weightedHartreeKernel r rho)
      halfLineMeasure := by
    have hm : Measurable (fun rho : ℝ => weightedHartreeKernel r rho) := by
      exact weightedHartreeKernel_uncurry_measurable.comp
        (measurable_const.prodMk measurable_id)
    exact hm.aestronglyMeasurable
  have hrow : MemLp (fun rho : ℝ => weightedHartreeKernel r rho) 2
      halfLineMeasure := by
    apply (memLp_two_iff_integrable_sq hrowMeas).2
    exact hrowSq
  let row : RealL2 halfLineMeasure :=
    hrow.toLp (fun rho : ℝ => weightedHartreeKernel r rho)
  have hrowAe : (row : ℝ → ℝ) =ᵐ[halfLineMeasure]
      fun rho => weightedHartreeKernel r rho := hrow.coeFn_toLp
  have hpoint : weightedHartreePointwise f r = inner ℝ row f := by
    unfold weightedHartreePointwise
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrowAe] with rho hρ
    rw [hρ, Real.inner_apply]
  have hintegral :
      (∫ rho : ℝ, weightedHartreeKernel r rho ^ 2
          ∂halfLineMeasure) =
        576 * weightedZeroGreen r r := by
    change (∫ rho in Ioi (0 : ℝ),
      weightedHartreeKernel r rho ^ 2) =
        576 * weightedZeroGreen r r
    calc
      (∫ rho in Ioi (0 : ℝ), weightedHartreeKernel r rho ^ 2) =
          ∫ rho in Ioi (0 : ℝ),
            weightedHartreeKernel r rho *
              weightedHartreeKernel rho r := by
        apply integral_congr_ae
        filter_upwards with rho
        rw [weightedHartreeKernel_symm rho r]
        ring
      _ = 576 * weightedZeroGreen r r :=
        weightedHartreeKernel_square_integral hr hr
  have hnormSq : ‖row‖ ^ 2 = 576 * weightedZeroGreen r r := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    calc
      (∫ x : ℝ, inner ℝ (row x) (row x) ∂halfLineMeasure) =
          ∫ rho : ℝ, weightedHartreeKernel r rho ^ 2
            ∂halfLineMeasure := by
        apply integral_congr_ae
        filter_upwards [hrowAe] with rho hρ
        rw [hρ, Real.inner_apply]
        ring
      _ = 576 * weightedZeroGreen r r := hintegral
  have hnormSqLe :
      ‖row‖ ^ 2 ≤
        (Real.sqrt (288 * Real.pi) * bubble r) ^ 2 := by
    rw [hnormSq]
    have hA := weightedZeroGreen_diag_le hr
    have hpi : 0 ≤ 288 * Real.pi := by positivity
    have hsqrt := Real.sq_sqrt hpi
    nlinarith
  have hnormLe :
      ‖row‖ ≤ Real.sqrt (288 * Real.pi) * bubble r := by
    apply (sq_le_sq₀ (norm_nonneg row)
      (mul_nonneg (Real.sqrt_nonneg _)
        (show 0 ≤ bubble r by unfold bubble; positivity))).mp
    exact hnormSqLe
  rw [hpoint]
  calc
    |inner ℝ row f| ≤ ‖row‖ * ‖f‖ := abs_real_inner_le_norm row f
    _ ≤ (Real.sqrt (288 * Real.pi) * bubble r) * ‖f‖ :=
      mul_le_mul_of_nonneg_right hnormLe (norm_nonneg f)

/-- In the original half-line variables the nonlocal term gains two more
powers of `W`, hence decays like `W³` almost everywhere. -/
theorem nonlocalApply_ae_norm_le_of_weighted_memLp
    (q : ℝ → ℝ)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2
      halfLineMeasure) :
    ∀ᵐ r ∂halfLineMeasure,
      |nonlocalApply q r| ≤
        Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
          ‖hq.toLp (fun rho => weightedGreenDecay rho * q rho)‖ := by
  let x : RealL2 halfLineMeasure :=
    hq.toLp (fun rho => weightedGreenDecay rho * q rho)
  filter_upwards [weightedHartreePointwise_ae_norm_le x,
    ae_restrict_mem measurableSet_Ioi] with r hbound hr
  have hconj : weightedHartreePointwise x r =
      (1 + r ^ 2) * nonlocalApply q r :=
    weightedHartreePointwise_conjugation q hq r
  have hden : 0 < 1 + r ^ 2 := by positivity
  have hN : |nonlocalApply q r| =
      (1 + r ^ 2)⁻¹ * |weightedHartreePointwise x r| := by
    rw [hconj, abs_mul, abs_of_pos hden]
    field_simp
  rw [hN]
  have ha0 : 0 ≤ (1 + r ^ 2)⁻¹ := by positivity
  calc
    (1 + r ^ 2)⁻¹ * |weightedHartreePointwise x r| ≤
        (1 + r ^ 2)⁻¹ *
          (Real.sqrt (288 * Real.pi) * bubble r * ‖x‖) :=
      mul_le_mul_of_nonneg_left hbound ha0
    _ = Real.sqrt (288 * Real.pi) * bubble r ^ 3 * ‖x‖ := by
      unfold bubble
      have hs : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
      have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
        Real.sq_sqrt (by positivity)
      field_simp [hs]
      rw [hs2]

end HBL.Modulation.Monopole
