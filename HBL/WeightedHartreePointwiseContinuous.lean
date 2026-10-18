import HBL.WeightedHartreePointwiseBound

/-!
Continuity of the actual weighted Hartree integral, obtained from the exact
Gram kernel of its square-integrable rows.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

theorem angularHartreeLog_sq_integrableOn
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    IntegrableOn (fun s : ℝ => angularHartreeLog theta s ^ 2)
      (Ioo 0 (Real.pi / 2)) := by
  have hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioc 0 Real.pi := by
    intro s hs
    exact ⟨hs.1, by linarith [hs.2, Real.pi_pos]⟩
  have hD := (HBL.memLp_angularLogDifference_Ioc theta).integrable_sq.mono_measure
    (Measure.restrict_mono_set volume hsub)
  refine hD.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    (Measure.ae_ne volume theta).filter_mono ae_restrict_le] with s hs hne
  rw [angularLogDifference_eq_angularHartreeLog htheta hs.1 hs.2 hne.symm]

theorem weightedHartreeKernel_row_sq_integrable
    {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun rho : ℝ => weightedHartreeKernel r rho ^ 2)
      halfLineMeasure := by
  let g : ℝ → ℝ := fun theta => angularHartreeLog (Real.arctan r) theta ^ 2
  have htheta : Real.arctan r ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨Real.arctan_nonneg.mpr hr, (Real.arctan_lt_pi_div_two r).le⟩
  have hg : IntegrableOn g (Ioo 0 (Real.pi / 2)) :=
    angularHartreeLog_sq_integrableOn htheta
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (0 : ℝ)) (f := Real.arctan)
    (f' := fun rho : ℝ => (1 + rho ^ 2)⁻¹)
    measurableSet_Ioi
    (fun rho _ => (Real.hasDerivAt_arctan' rho).hasDerivWithinAt)
    Real.arctan_injective.injOn g
  rw [arctan_image_Ioi] at hchange
  have hpull : IntegrableOn
      (fun rho : ℝ => bubble rho ^ 2 * g (Real.arctan rho)) (Ioi 0) := by
    refine (hchange.mp hg).congr_fun ?_ measurableSet_Ioi
    intro rho _
    change |(1 + rho ^ 2)⁻¹| * g (Real.arctan rho) =
      bubble rho ^ 2 * g (Real.arctan rho)
    rw [abs_of_pos (by positivity : 0 < (1 + rho ^ 2)⁻¹),
      bubble_sq]
  have hscaled := hpull.const_mul ((24 / Real.pi * bubble r) ^ 2)
  refine hscaled.congr ?_
  filter_upwards [(Measure.ae_ne volume r).filter_mono ae_restrict_le]
    with rho hne
  rw [weightedHartreeKernel_eq_angular r rho hne.symm]
  dsimp only [g]
  ring

theorem weightedHartreeKernel_row_memLp
    {r : ℝ} (hr : 0 ≤ r) :
    MemLp (weightedHartreeKernel r) 2 halfLineMeasure := by
  have hm : AEStronglyMeasurable (weightedHartreeKernel r) halfLineMeasure :=
    (weightedHartreeKernel_uncurry_measurable.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hm).2
    (weightedHartreeKernel_row_sq_integrable hr)

/-- The genuine kernel row, as an `L²` element on the closed half-line. -/
def weightedHartreeRow (r : Ici (0 : ℝ)) : RealL2 halfLineMeasure :=
  (weightedHartreeKernel_row_memLp r.property).toLp
    (weightedHartreeKernel r.val)

theorem weightedHartreeRow_ae (r : Ici (0 : ℝ)) :
    (weightedHartreeRow r : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedHartreeKernel r.val :=
  (weightedHartreeKernel_row_memLp r.property).coeFn_toLp

theorem weightedHartreeKernel_zero_left (rho : ℝ) :
    weightedHartreeKernel 0 rho = 0 := by
  unfold weightedHartreeKernel hartreeRadialLog
  by_cases hzero : rho = 0
  · simp [hzero]
  · rw [zero_add, zero_sub, abs_neg]
    rw [Real.log_div hzero (abs_ne_zero.mpr hzero), Real.log_abs]
    simp

theorem weightedZeroGreen_zero_left {rho : ℝ} (hrho : 0 ≤ rho) :
    weightedZeroGreen 0 rho = 0 := by
  unfold weightedZeroGreen angularZeroGreen
  simp [Real.arctan_zero, min_eq_left (Real.arctan_nonneg.mpr hrho)]

theorem weightedZeroGreen_symm (r rho : ℝ) :
    weightedZeroGreen r rho = weightedZeroGreen rho r := by
  unfold weightedZeroGreen angularZeroGreen
  rw [min_comm (Real.arctan r), max_comm (Real.arctan r)]
  ring

theorem weightedHartreeRow_inner (r rho : Ici (0 : ℝ)) :
    inner ℝ (weightedHartreeRow r) (weightedHartreeRow rho) =
      576 * weightedZeroGreen r.val rho.val := by
  rw [L2.inner_def]
  have heq :
      (∫ s : ℝ, inner ℝ (weightedHartreeRow r s) (weightedHartreeRow rho s)
          ∂halfLineMeasure) =
        ∫ s in Ioi (0 : ℝ),
          weightedHartreeKernel r.val s * weightedHartreeKernel s rho.val := by
    apply integral_congr_ae
    filter_upwards [weightedHartreeRow_ae r, weightedHartreeRow_ae rho]
      with s hr hs
    rw [hr, hs, Real.inner_apply, weightedHartreeKernel_symm s rho.val]
  rw [heq]
  by_cases hr : r.val = 0
  · rw [hr, weightedZeroGreen_zero_left rho.property]
    simp only [weightedHartreeKernel_zero_left, zero_mul, integral_zero, mul_zero]
  by_cases hrho : rho.val = 0
  · rw [hrho, weightedZeroGreen_symm r.val 0,
      weightedZeroGreen_zero_left r.property]
    have hk : ∀ s : ℝ, weightedHartreeKernel s 0 = 0 := by
      intro s
      rw [weightedHartreeKernel_symm, weightedHartreeKernel_zero_left]
    simp only [hk, mul_zero, integral_zero]
  exact weightedHartreeKernel_square_integral
    (lt_of_le_of_ne r.property (Ne.symm hr))
    (lt_of_le_of_ne rho.property (Ne.symm hrho))

theorem weightedHartreeRow_norm_sub_sq (r rho : Ici (0 : ℝ)) :
    ‖weightedHartreeRow r - weightedHartreeRow rho‖ ^ 2 =
      576 * (weightedZeroGreen r.val r.val -
        2 * weightedZeroGreen r.val rho.val + weightedZeroGreen rho.val rho.val) := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, weightedHartreeRow_inner,
    weightedHartreeRow_inner, weightedHartreeRow_inner]
  ring

theorem weightedHartreeRow_continuous : Continuous weightedHartreeRow := by
  apply continuous_iff_continuousAt.2
  intro r
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hdiag : Continuous (fun rho : Ici (0 : ℝ) =>
      weightedZeroGreen rho.val rho.val) :=
    weightedZeroGreen_uncurry_continuous.comp
      (continuous_subtype_val.prodMk continuous_subtype_val)
  have hcross : Continuous (fun rho : Ici (0 : ℝ) =>
      weightedZeroGreen rho.val r.val) :=
    weightedZeroGreen_uncurry_continuous.comp
      (continuous_subtype_val.prodMk continuous_const)
  have hD : Continuous (fun rho : Ici (0 : ℝ) =>
      576 * (weightedZeroGreen rho.val rho.val -
        2 * weightedZeroGreen rho.val r.val + weightedZeroGreen r.val r.val)) :=
    (hdiag.sub (hcross.const_mul 2) |>.add continuous_const).const_mul 576
  have hlim := (hD.continuousAt (x := r)).sqrt.tendsto
  simpa only [← weightedHartreeRow_norm_sub_sq,
    Real.sqrt_sq_eq_abs, abs_norm, sub_self, norm_zero, abs_zero] using hlim

theorem weightedHartreePointwise_eq_inner
    (f : RealL2 halfLineMeasure) (r : Ici (0 : ℝ)) :
    weightedHartreePointwise f r.val = inner ℝ (weightedHartreeRow r) f := by
  unfold weightedHartreePointwise
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightedHartreeRow_ae r] with rho hrow
  rw [hrow, Real.inner_apply]

theorem weightedHartreePointwise_continuous_nonnegative
    (f : RealL2 halfLineMeasure) :
    Continuous (fun r : Ici (0 : ℝ) => weightedHartreePointwise f r.val) := by
  simpa only [weightedHartreePointwise_eq_inner] using
    weightedHartreeRow_continuous.inner
      (continuous_const : Continuous (fun _ : Ici (0 : ℝ) => f))

theorem weightedHartreePointwise_zero (f : RealL2 halfLineMeasure) :
    weightedHartreePointwise f 0 = 0 := by
  simp [weightedHartreePointwise, weightedHartreeKernel_zero_left]

theorem hartreeRadialLog_neg_left (r rho : ℝ) :
    hartreeRadialLog (-r) rho = -hartreeRadialLog r rho := by
  by_cases hsub : r = rho
  · subst r
    simp [hartreeRadialLog]
  by_cases hsum : r = -rho
  · subst r
    simp [hartreeRadialLog]
  have hsub' : r - rho ≠ 0 := sub_ne_zero.mpr hsub
  have hsum' : r + rho ≠ 0 := by
    intro hz
    apply hsum
    linarith
  have hleft : -r + rho ≠ 0 := by
    intro hz
    apply hsub
    linarith
  have habs : |-r - rho| ≠ 0 := by
    apply abs_ne_zero.mpr
    intro hz
    apply hsum'
    linarith
  unfold hartreeRadialLog
  rw [Real.log_div hleft habs,
    Real.log_div hsum' (abs_ne_zero.mpr hsub'),
    Real.log_abs, Real.log_abs,
    show -r + rho = -(r - rho) by ring,
    show -r - rho = -(r + rho) by ring,
    Real.log_neg_eq_log, Real.log_neg_eq_log]
  ring

theorem weightedHartreeKernel_neg_left (r rho : ℝ) :
    weightedHartreeKernel (-r) rho = -weightedHartreeKernel r rho := by
  unfold weightedHartreeKernel
  rw [hartreeRadialLog_neg_left]
  have hb : bubble (-r) = bubble r := by simp [bubble]
  rw [hb]
  ring

theorem weightedHartreePointwise_neg
    (f : RealL2 halfLineMeasure) (r : ℝ) :
    weightedHartreePointwise f (-r) = -weightedHartreePointwise f r := by
  simp only [weightedHartreePointwise, weightedHartreeKernel_neg_left,
    neg_mul, integral_neg]

/-- The original Lebesgue integral, including the endpoint and its natural
odd extension to the real line, is continuous. -/
theorem weightedHartreePointwise_continuous
    (f : RealL2 halfLineMeasure) : Continuous (weightedHartreePointwise f) := by
  let F : ℝ → ℝ := fun r => weightedHartreePointwise f (max r 0)
  have hmax : Continuous (fun r : ℝ =>
      (⟨max r 0, le_max_right r 0⟩ : Ici (0 : ℝ))) :=
    (continuous_id.max continuous_const).subtype_mk _
  have hF : Continuous F :=
    (weightedHartreePointwise_continuous_nonnegative f).comp hmax
  have hrep : weightedHartreePointwise f = fun r => F r - F (-r) := by
    funext r
    dsimp only [F]
    by_cases hr : 0 ≤ r
    · rw [max_eq_left hr, max_eq_right (by linarith : -r ≤ 0),
        weightedHartreePointwise_zero, sub_zero]
    · have hr' : r ≤ 0 := le_of_lt (lt_of_not_ge hr)
      rw [max_eq_right hr', max_eq_left (by linarith : 0 ≤ -r),
        weightedHartreePointwise_zero, zero_sub,
        weightedHartreePointwise_neg, neg_neg]
  rw [hrep]
  exact hF.sub (hF.comp continuous_neg)

theorem nonlocalApply_continuous_of_weighted_memLp
    (q : ℝ → ℝ)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure) :
    Continuous (nonlocalApply q) := by
  let f : RealL2 halfLineMeasure :=
    hq.toLp (fun r => weightedGreenDecay r * q r)
  have hrep : nonlocalApply q = fun r =>
      (1 + r ^ 2)⁻¹ * weightedHartreePointwise f r := by
    funext r
    rw [weightedHartreePointwise_conjugation]
    field_simp [show (1 + r ^ 2 : ℝ) ≠ 0 by positivity]
  rw [hrep]
  have hweight : Continuous (fun r : ℝ => (1 + r ^ 2)⁻¹) := by
    exact (continuous_const.add (continuous_id.pow 2)).inv₀
      (fun r => by change (1 + r ^ 2 : ℝ) ≠ 0; positivity)
  exact hweight.mul (weightedHartreePointwise_continuous f)

end HBL.Modulation.Monopole
