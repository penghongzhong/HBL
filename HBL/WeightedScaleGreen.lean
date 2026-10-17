import HBL.WeightedScaleResonance

/-!
The differential source and the zero-slope Green identity for the actual
weighted scaling resonance.  These are the analytic ingredients needed to
turn the already certified pointwise equation `H₊ ψ₊ = 0` into the concrete
Birman--Schwinger fixed-vector equation.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- The scale resonance has the exact local second-order equation used by
the weighted free Green operator. -/
theorem resonancePlus_second_eq_weight (r : ℝ) :
    -deriv (deriv resonancePlus) r =
      15 * (1 + r ^ 2)⁻¹ ^ 2 * resonancePlus r := by
  rw [resonancePlus_second_from_minus, resonanceMinus_def,
    resonancePlus_def, dilationGenerator_bubble_closed]
  have hd : deriv resonanceMinus r = bubbleRadialEnergyDerivative r := by
    change deriv (radialU bubble) r = bubbleRadialEnergyDerivative r
    exact radialU_bubble_deriv_closed r
  rw [hd]
  have hs : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold potential potentialDerivative bubble
    bubbleRadialEnergyDerivative
  field_simp [hs]
  rw [hs2]
  ring

/-- The unweighted source seen by the Dirichlet Green kernel. -/
def weightedScaleGreenSource (r : ℝ) : ℝ :=
  15 * (1 + r ^ 2)⁻¹ ^ 2 * resonancePlus r

theorem weightedScaleGreenSource_eq_neg_second (r : ℝ) :
    weightedScaleGreenSource r = -deriv (deriv resonancePlus) r := by
  unfold weightedScaleGreenSource
  rw [resonancePlus_second_eq_weight]

theorem weightedScaleGreenSource_continuous :
    Continuous weightedScaleGreenSource := by
  unfold weightedScaleGreenSource
  have hden : Continuous (fun r : ℝ => 1 + r ^ 2) := by fun_prop
  exact (continuous_const.mul
    ((hden.inv₀ (fun r => by positivity)).pow 2)).mul
      resonancePlus_contDiff_infty.continuous

theorem weightedScaleGreenSource_integrable :
    Integrable weightedScaleGreenSource := by
  have hmajor : Integrable (fun r : ℝ =>
      (15 / 2 : ℝ) * (1 + r ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (15 / 2 : ℝ)
  refine hmajor.mono' weightedScaleGreenSource_continuous.aestronglyMeasurable ?_
  filter_upwards with r
  rw [Real.norm_eq_abs]
  have ha0 : 0 ≤ (1 + r ^ 2)⁻¹ := by positivity
  have ha1 : (1 + r ^ 2)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity : 0 < 1 + r ^ 2)).2
      (by nlinarith [sq_nonneg r])
  have hpsi : |resonancePlus r| ≤ 1 / 2 := by
    by_cases hr : 0 ≤ r
    · exact resonancePlus_abs_le_half r hr
    · rw [resonancePlus_def, dilationGenerator_bubble_closed,
        abs_mul, abs_div]
      have hclosed := resonancePlus_abs_le_half (-r) (by linarith)
      rw [resonancePlus_def, dilationGenerator_bubble_closed,
        neg_sq, abs_mul, abs_div, abs_neg] at hclosed
      simpa [abs_neg] using hclosed
  rw [weightedScaleGreenSource, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15),
    abs_of_nonneg (by positivity :
      0 ≤ (1 + r ^ 2)⁻¹ ^ 2)]
  calc
    15 * (1 + r ^ 2)⁻¹ ^ 2 * |resonancePlus r| ≤
        15 * (1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) :=
      mul_le_mul_of_nonneg_left hpsi (by positivity)
    _ ≤ (15 / 2 : ℝ) * (1 + r ^ 2)⁻¹ := by
      nlinarith [mul_self_le_mul_self ha0 ha1]

theorem resonancePlus_deriv_tendsto_zero :
    Tendsto (deriv resonancePlus) atTop (𝓝 (0 : ℝ)) := by
  have h := radius_resonancePlus_deriv_tendsto_zero.mul
    tendsto_inv_atTop_zero
  have heq :
      (fun r : ℝ => (r * deriv resonancePlus r) * r⁻¹) =ᶠ[atTop]
        deriv resonancePlus := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr
    field_simp
  simpa only [zero_mul] using h.congr' heq

/-- Finite left part of the zero-slope Green identity. -/
theorem weightedScaleGreenSource_left (r : ℝ) :
    (∫ rho in (0 : ℝ)..r, rho * weightedScaleGreenSource rho) =
      resonancePlus r - r * deriv resonancePlus r := by
  have hpsi : ContDiff ℝ ∞ resonancePlus := resonancePlus_contDiff_infty
  have hpsi1 : ContDiff ℝ ∞ (deriv resonancePlus) :=
    (contDiff_infty_iff_deriv.mp hpsi).2
  have hD (rho : ℝ) :
      HasDerivAt resonancePlus (deriv resonancePlus rho) rho :=
    ((contDiff_infty_iff_deriv.mp hpsi).1 rho).hasDerivAt
  have hDD (rho : ℝ) :
      HasDerivAt (deriv resonancePlus)
        (deriv (deriv resonancePlus) rho) rho :=
    ((contDiff_infty_iff_deriv.mp hpsi1).1 rho).hasDerivAt
  have hprim (rho : ℝ) : HasDerivAt
      (fun x : ℝ => resonancePlus x - x * deriv resonancePlus x)
      (rho * weightedScaleGreenSource rho) rho := by
    have h := (hD rho).sub ((hasDerivAt_id rho).mul (hDD rho))
    convert h using 1
    · funext x
      rfl
    · rw [weightedScaleGreenSource_eq_neg_second]
      simp only [id_eq]
      ring
  have hint : IntervalIntegrable
      (fun rho : ℝ => rho * weightedScaleGreenSource rho) volume 0 r :=
    (continuous_id.mul weightedScaleGreenSource_continuous).intervalIntegrable 0 r
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun rho _ => hprim rho) hint
  simpa [resonancePlus_zero] using hftc

/-- Tail integral of the source is the outgoing derivative. -/
theorem weightedScaleGreenSource_tail (r : ℝ) :
    (∫ rho in Ioi r, weightedScaleGreenSource rho) =
      deriv resonancePlus r := by
  have hint : IntegrableOn weightedScaleGreenSource (Ioi r) :=
    weightedScaleGreenSource_integrable.integrableOn
  have hIntegral := intervalIntegral_tendsto_integral_Ioi r hint tendsto_id
  have hpsi : ContDiff ℝ ∞ resonancePlus := resonancePlus_contDiff_infty
  have hpsi1 : ContDiff ℝ ∞ (deriv resonancePlus) :=
    (contDiff_infty_iff_deriv.mp hpsi).2
  have hfinite (R : ℝ) :
      (∫ rho in r..R, weightedScaleGreenSource rho) =
        deriv resonancePlus r - deriv resonancePlus R := by
    have hprim (rho : ℝ) :
        HasDerivAt (fun x : ℝ => -deriv resonancePlus x)
          (weightedScaleGreenSource rho) rho := by
      have h := ((contDiff_infty_iff_deriv.mp hpsi1).1 rho).hasDerivAt.neg
      convert h using 1
      exact weightedScaleGreenSource_eq_neg_second rho
    have hint' : IntervalIntegrable weightedScaleGreenSource volume r R :=
      weightedScaleGreenSource_continuous.intervalIntegrable r R
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun rho _ => hprim rho) hint'
    simpa [sub_eq_add_neg, add_comm] using hftc
  have hBoundary : Tendsto
      (fun R : ℝ => ∫ rho in r..R, weightedScaleGreenSource rho)
      atTop (𝓝 (deriv resonancePlus r)) := by
    have hconst : Tendsto (fun _ : ℝ => deriv resonancePlus r) atTop
        (𝓝 (deriv resonancePlus r)) := tendsto_const_nhds
    have h := hconst.sub resonancePlus_deriv_tendsto_zero
    simpa only [sub_zero] using h.congr'
      (Filter.Eventually.of_forall fun R => (hfinite R).symm)
  exact tendsto_nhds_unique hIntegral hBoundary

/-- Pointwise inversion by the unweighted half-line kernel `min r rho`. -/
theorem min_weightedScaleGreenSource_integral
    (r : ℝ) (hr : 0 < r) :
    (∫ rho in Ioi (0 : ℝ),
      min r rho * weightedScaleGreenSource rho) = resonancePlus r := by
  have hleftInt : IntegrableOn
      (fun rho : ℝ => min r rho * weightedScaleGreenSource rho)
      (Ioc (0 : ℝ) r) := by
    exact ((continuous_const.min continuous_id).mul
      weightedScaleGreenSource_continuous).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
  have htailInt : IntegrableOn
      (fun rho : ℝ => min r rho * weightedScaleGreenSource rho)
      (Ioi r) := by
    refine (weightedScaleGreenSource_integrable.const_mul r).integrableOn.congr_fun ?_
      measurableSet_Ioi
    intro rho hρ
    change r * weightedScaleGreenSource rho =
      min r rho * weightedScaleGreenSource rho
    rw [min_eq_left hρ.le]
  rw [← Ioc_union_Ioi_eq_Ioi hr.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hleftInt htailInt]
  have hleft :
      (∫ rho in Ioc (0 : ℝ) r,
        min r rho * weightedScaleGreenSource rho) =
        ∫ rho in (0 : ℝ)..r, rho * weightedScaleGreenSource rho := by
    rw [intervalIntegral.integral_of_le hr.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro rho hρ
    change min r rho * weightedScaleGreenSource rho =
      rho * weightedScaleGreenSource rho
    rw [min_eq_right hρ.2]
  have htail :
      (∫ rho in Ioi r,
        min r rho * weightedScaleGreenSource rho) =
        r * ∫ rho in Ioi r, weightedScaleGreenSource rho := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro rho hρ
    change min r rho * weightedScaleGreenSource rho =
      r * weightedScaleGreenSource rho
    rw [min_eq_left hρ.le]
  rw [hleft, htail, weightedScaleGreenSource_left,
    weightedScaleGreenSource_tail]
  ring

/-- Weak integral action of the concrete weighted free Green operator. -/
theorem weightedFreeGreenOperator_weak_apply
    (f g : RealL2 halfLineMeasure) :
    inner ℝ (weightedFreeGreenOperator f) g =
      ∫ p : ℝ × ℝ,
        weightedFreeGreen p.1 p.2 * (g p.1 * f p.2)
        ∂(halfLineMeasure.prod halfLineMeasure) := by
  change inner ℝ (operator weightedFreeGreenL2 f) g = _
  rw [inner_operator, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightedFreeGreenL2_ae, tensor_ae g f] with p hK ht
  rw [hK, ht, Real.inner_apply]
  rfl

/-- The free Green factor sends `15 x₀` exactly to the actual weighted scale
resonance `x₀`. -/
theorem weightedFreeGreenOperator_scale_eigen :
    weightedFreeGreenOperator
        ((15 : ℝ) • weightedScaleResonanceL2) =
      weightedScaleResonanceL2 := by
  apply ext_inner_right ℝ
  intro g
  rw [weightedFreeGreenOperator_weak_apply]
  let f : RealL2 halfLineMeasure :=
    (15 : ℝ) • weightedScaleResonanceL2
  have hf_ae : (f : ℝ → ℝ) =ᵐ[halfLineMeasure]
      fun rho => 15 * weightedScaleResonance rho := by
    dsimp [f]
    filter_upwards [Lp.coeFn_smul (15 : ℝ) weightedScaleResonanceL2,
      weightedScaleResonanceL2_ae] with rho hsmul hx0
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul, hx0]
  have hprod : Integrable (fun p : ℝ × ℝ =>
      weightedFreeGreen p.1 p.2 * (g p.1 * f p.2))
      (halfLineMeasure.prod halfLineMeasure) := by
    have h := weightedFreeGreen_memLp_two.integrable_mul
      (Lp.memLp (tensor g f))
    refine h.congr ?_
    filter_upwards [tensor_ae g f] with p ht
    change weightedFreeGreen p.1 p.2 * (tensor g f : ℝ × ℝ → ℝ) p = _
    rw [ht]
  change (∫ p : ℝ × ℝ,
      weightedFreeGreen p.1 p.2 * (g p.1 * f p.2)
      ∂(halfLineMeasure.prod halfLineMeasure)) = _
  rw [integral_prod _ hprod]
  have hinner :
      (fun r : ℝ => ∫ rho : ℝ,
        weightedFreeGreen r rho * (g r * f rho) ∂halfLineMeasure) =ᵐ[
          halfLineMeasure]
      fun r => (1 + r ^ 2)⁻¹ * g r * resonancePlus r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    calc
      (∫ rho : ℝ,
          weightedFreeGreen r rho * (g r * f rho) ∂halfLineMeasure) =
          ∫ rho : ℝ,
            ((1 + r ^ 2)⁻¹ * g r) *
              (min r rho * weightedScaleGreenSource rho)
            ∂halfLineMeasure := by
        apply integral_congr_ae
        filter_upwards [hf_ae] with rho hρ
        rw [hρ, weightedScaleResonance_closed]
        unfold weightedFreeGreen weightedScaleGreenSource
        ring
      _ = (1 + r ^ 2)⁻¹ * g r *
          (∫ rho : ℝ, min r rho * weightedScaleGreenSource rho
            ∂halfLineMeasure) := by
        rw [integral_const_mul]
      _ = (1 + r ^ 2)⁻¹ * g r * resonancePlus r := by
        change (1 + r ^ 2)⁻¹ * g r *
          (∫ rho in Ioi (0 : ℝ),
            min r rho * weightedScaleGreenSource rho) = _
        rw [min_weightedScaleGreenSource_integral r hr]
  rw [integral_congr_ae hinner, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightedScaleResonanceL2_ae] with r hx0
  rw [hx0, Real.inner_apply, weightedScaleResonance_closed]
  ring

/-- The certified equation `H₊ ψ₊ = 0`, together with the explicit second
derivative, evaluates its nonlocal term. -/
theorem nonlocalApply_resonancePlus_eq_six_weight
    (r : ℝ) (hr : 0 < r) :
    nonlocalApply resonancePlus r =
      6 * (1 + r ^ 2)⁻¹ ^ 2 * resonancePlus r := by
  have hz := hPlus_resonancePlus_zero r hr
  unfold hPlusApply at hz
  rw [resonancePlus_second_eq_weight] at hz
  unfold potential at hz
  rw [div_eq_mul_inv] at hz
  rw [← inv_pow] at hz
  linarith

/-- Pointwise action of the conjugated Hartree kernel on `x₀`. -/
theorem weightedHartree_scale_integral
    (r : ℝ) (hr : 0 < r) :
    (∫ rho : ℝ,
      weightedHartreeKernel r rho * weightedScaleResonance rho
      ∂halfLineMeasure) = 6 * weightedScaleResonance r := by
  have hbr : bubble r ^ 2 = (1 + r ^ 2)⁻¹ := by
    simpa only [birmanSquareWeight] using birmanSquareWeight_closed r
  calc
    (∫ rho : ℝ,
        weightedHartreeKernel r rho * weightedScaleResonance rho
        ∂halfLineMeasure) =
        (1 + r ^ 2) * nonlocalApply resonancePlus r := by
      rw [halfLineMeasure]
      unfold nonlocalApply
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro rho hρ
      have hbρ : bubble rho ^ 2 = (1 + rho ^ 2)⁻¹ := by
        simpa only [birmanSquareWeight] using birmanSquareWeight_closed rho
      change weightedHartreeKernel r rho * weightedScaleResonance rho =
        (1 + r ^ 2) * (hartreeKernel r rho * resonancePlus rho)
      rw [weightedScaleResonance_closed]
      unfold weightedHartreeKernel hartreeKernel hartreeRadialLog
      rw [show bubble r ^ 3 = bubble r * (1 + r ^ 2)⁻¹ by
          calc
            bubble r ^ 3 = bubble r * bubble r ^ 2 := by ring
            _ = bubble r * (1 + r ^ 2)⁻¹ := by rw [hbr],
        show bubble rho ^ 3 = bubble rho * (1 + rho ^ 2)⁻¹ by
          calc
            bubble rho ^ 3 = bubble rho * bubble rho ^ 2 := by ring
            _ = bubble rho * (1 + rho ^ 2)⁻¹ := by rw [hbρ]]
      field_simp
    _ = (1 + r ^ 2) *
        (6 * (1 + r ^ 2)⁻¹ ^ 2 * resonancePlus r) := by
      rw [nonlocalApply_resonancePlus_eq_six_weight r hr]
    _ = 6 * weightedScaleResonance r := by
      rw [weightedScaleResonance_closed]
      field_simp

/-- Weak integral action of the concrete conjugated Hartree operator. -/
theorem weightedHartreeOperator_weak_apply
    (f g : RealL2 halfLineMeasure) :
    inner ℝ (weightedHartreeOperator f) g =
      ∫ p : ℝ × ℝ,
        weightedHartreeKernel p.1 p.2 * (g p.1 * f p.2)
        ∂(halfLineMeasure.prod halfLineMeasure) := by
  change inner ℝ (operator weightedHartreeKernelL2 f) g = _
  rw [inner_operator, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightedHartreeKernelL2_ae, tensor_ae g f] with p hK ht
  rw [hK, ht, Real.inner_apply]
  rfl

/-- The conjugated Hartree factor has eigenvalue six on the actual weighted
scale resonance. -/
theorem weightedHartreeOperator_scale_eigen :
    weightedHartreeOperator weightedScaleResonanceL2 =
      (6 : ℝ) • weightedScaleResonanceL2 := by
  apply ext_inner_right ℝ
  intro g
  rw [weightedHartreeOperator_weak_apply]
  let f : RealL2 halfLineMeasure := weightedScaleResonanceL2
  have hprod : Integrable (fun p : ℝ × ℝ =>
      weightedHartreeKernel p.1 p.2 * (g p.1 * f p.2))
      (halfLineMeasure.prod halfLineMeasure) := by
    have h := weightedHartreeKernel_memLp_two.integrable_mul
      (Lp.memLp (tensor g f))
    refine h.congr ?_
    filter_upwards [tensor_ae g f] with p ht
    change weightedHartreeKernel p.1 p.2 * (tensor g f : ℝ × ℝ → ℝ) p = _
    rw [ht]
  change (∫ p : ℝ × ℝ,
      weightedHartreeKernel p.1 p.2 * (g p.1 * f p.2)
      ∂(halfLineMeasure.prod halfLineMeasure)) = _
  rw [integral_prod _ hprod]
  have hinner :
      (fun r : ℝ => ∫ rho : ℝ,
        weightedHartreeKernel r rho * (g r * f rho) ∂halfLineMeasure) =ᵐ[
          halfLineMeasure]
      fun r => g r * (6 * weightedScaleResonance r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    calc
      (∫ rho : ℝ,
          weightedHartreeKernel r rho * (g r * f rho)
          ∂halfLineMeasure) =
          g r * (∫ rho : ℝ,
            weightedHartreeKernel r rho * weightedScaleResonance rho
            ∂halfLineMeasure) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [weightedScaleResonanceL2_ae] with rho hρ
        change weightedHartreeKernel r rho * (g r * f rho) =
          g r * (weightedHartreeKernel r rho * weightedScaleResonance rho)
        rw [show f rho = weightedScaleResonance rho by exact hρ]
        ring
      _ = g r * (6 * weightedScaleResonance r) := by
        rw [weightedHartree_scale_integral r hr]
  rw [integral_congr_ae hinner, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul (6 : ℝ) weightedScaleResonanceL2,
    weightedScaleResonanceL2_ae] with r hsmul hx0
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul, hx0, Real.inner_apply]
  change g r * (6 * weightedScaleResonance r) =
    (6 * weightedScaleResonance r) * g r
  ring

/-- The full conjugated potential has eigenvalue fifteen on `x₀`. -/
theorem weightedPotentialOperator_scale_eigen :
    weightedPotentialOperator weightedScaleResonanceL2 =
      (15 : ℝ) • weightedScaleResonanceL2 := by
  unfold weightedPotentialOperator
  rw [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, weightedHartreeOperator_scale_eigen]
  module

/-- The actual weighted scale resonance is an unconditional fixed vector of
the concrete Birman--Schwinger operator. -/
theorem weightedBirmanSchwinger_scale_fixed :
    weightedBirmanSchwingerOperator weightedScaleResonanceL2 =
      weightedScaleResonanceL2 := by
  unfold weightedBirmanSchwingerOperator
  rw [ContinuousLinearMap.comp_apply,
    weightedPotentialOperator_scale_eigen]
  exact weightedFreeGreenOperator_scale_eigen

/-- The Fredholm cokernel pairing for the actual scale vector now has no
remaining fixed-vector premise. -/
theorem weightedScaleResonance_cokernel_pairing
    (F : RealL2 halfLineMeasure) :
    inner ℝ (weightedPotentialOperator weightedScaleResonanceL2)
        (weightedFreeGreenOperator F) =
      inner ℝ weightedScaleResonanceL2 F :=
  weightedBirmanSchwinger_cokernel_pairing weightedScaleResonanceL2 F
    weightedBirmanSchwinger_scale_fixed

end HBL.Modulation.Monopole
