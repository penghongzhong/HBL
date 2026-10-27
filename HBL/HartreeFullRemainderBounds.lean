import HBL.HartreeDensitySourceBounds

/-!
# Full physical Hartree remainder in L2 and L-infinity

These are direct estimates for `PhysicalExpansion.remainder`, not assumptions
on an abstract nonlinear map. The background needs L4 and L-infinity, not L2.
The perturbation is controlled in L2 and L-infinity. Both the local cubic
factor and every nonlocal density term are retained. No derivative estimate,
local Lipschitz estimate, constrained propagator or PDE orbit is concluded.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
namespace HBL.RegularRadiation.PhysicalExpansion

/-- Linear density potential coefficient on a mixed L2/L-infinity ball. -/
def linearPotentialConstant (M J : ℝ) : ℝ :=
  4 * nearMass * M ^ 3 + 2 * M * (J + 1)

/-- Quadratic density potential coefficient. -/
def quadraticPotentialConstant (M r : ℝ) : ℝ :=
  densityQuadraticConstant M r * (nearMass + 1)

/-- Coefficient of r*|h| in the complete seventh-order remainder. -/
def fullRemainderHConstant (M r J : ℝ) : ℝ :=
  (nearMass * M ^ 4 + J) * (3 * M + r) +
    (linearPotentialConstant M J + quadraticPotentialConstant M r * r) *
      (3 * M ^ 2 + (3 * M + r) * r)

private theorem constants_nonneg {M r J : ℝ}
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hJ : 0 ≤ J) :
    0 ≤ linearPotentialConstant M J ∧
    0 ≤ quadraticPotentialConstant M r ∧
    0 ≤ fullRemainderHConstant M r J := by
  have hn := regularRadiationKernel_checks.2.1
  unfold fullRemainderHConstant linearPotentialConstant
    quadraticPotentialConstant densityQuadraticConstant
  exact ⟨by positivity, by positivity, by positivity⟩

private theorem background_density_integrable (w : Space → ℝ)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4)) :
    Integrable (quarticDensity (fun y => (w y : ℂ))) := by
  have hc : Integrable (fun y : Space => ((|w y| ^ 4 : ℝ) : ℂ)) := hw4.ofReal
  change Integrable (fun y : Space => ((‖(w y : ℂ)‖ ^ 4 : ℝ) : ℂ))
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hc

private theorem background_potential_bound (w : Space → ℝ)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4))
    {M : ℝ} (hwb : ∀ᵐ y, |w y| ≤ M) (x : Space) :
    ‖potential (quarticDensity (fun y => (w y : ℂ))) x‖ ≤
      nearMass * M ^ 4 + ∫ y : Space, |w y| ^ 4 := by
  have hb : ∀ᵐ y, ‖quarticDensity (fun v => (w v : ℂ)) y‖ ≤ M ^ 4 := by
    filter_upwards [hwb] with y hy
    simpa only [quarticDensity, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (abs_nonneg (w y)) 4)] using
      pow_le_pow_left₀ (abs_nonneg (w y)) hy 4
  have h := (potential_bound _ (background_density_integrable w hw4)
    (M ^ 4) (by positivity) hb x).2
  have he : (∫ y : Space, ‖quarticDensity (fun v => (w v : ℂ)) y‖) =
      ∫ y : Space, |w y| ^ 4 := by
    apply integral_congr_ae
    filter_upwards with y
    simp only [quarticDensity, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (abs_nonneg (w y)) 4)]
  rwa [he] at h

private theorem linear_density_scaled_bound (a : ℝ) (z : ℂ)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r) (ha : |a| ≤ M) :
    ‖((4 * a ^ 3 * z.re : ℝ) : ℂ)‖ ≤
      (2 * M) * (r * |a| ^ 4 + r⁻¹ * ‖z‖ ^ 2) := by
  have hc : 2 * |a| ^ 2 * ‖z‖ ≤ (r ^ 2 * |a| ^ 4 + ‖z‖ ^ 2) / r := by
    apply (le_div_iff₀ hr).2
    nlinarith only [sq_nonneg (r * |a| ^ 2 - ‖z‖)]
  have he : (r ^ 2 * |a| ^ 4 + ‖z‖ ^ 2) / r =
      r * |a| ^ 4 + r⁻¹ * ‖z‖ ^ 2 := by
    field_simp
  rw [he] at hc
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4 * |a| ^ 3 * ‖z‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (by positivity)
    _ = (2 * |a|) * (2 * |a| ^ 2 * ‖z‖) := by ring
    _ ≤ (2 * M) * (r * |a| ^ 4 + r⁻¹ * ‖z‖ ^ 2) :=
      mul_le_mul (by linarith) hc (by positivity) (by positivity)

/-- The linear density potential is genuinely first order in r. -/
theorem densityLinear_potential_small
    (w : Space → ℝ) (h : Space → ℂ) (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4)) (hh : MemLp h 2)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r)
    (hE : (∫ y : Space, ‖h y‖ ^ 2) ≤ r ^ 2) (x : Space) :
    ‖potential (densityLinear w h) x‖ ≤
      linearPotentialConstant M (∫ y : Space, |w y| ^ 4) * r := by
  have hi := (densityLinear_source_integrable w h hw hw4 hh hM hr.le hwb hhb).1
  have hdom : ∀ᵐ y, ‖densityLinear w h y‖ ≤
      (2 * M) * (r * |w y| ^ 4 + r⁻¹ * ‖h y‖ ^ 2) := by
    filter_upwards [hwb] with y hy
    exact linear_density_scaled_bound (w y) (h y) hM hr hy
  have hI := integral_mono_ae hi.norm
    (((hw4.const_mul r).add (hh.norm.integrable_sq.const_mul r⁻¹)).const_mul (2 * M)) hdom
  simp only [Pi.add_apply] at hI
  rw [integral_const_mul,
    integral_add (hw4.const_mul r) (hh.norm.integrable_sq.const_mul r⁻¹),
    integral_const_mul, integral_const_mul] at hI
  have he : r⁻¹ * r ^ 2 = r := by
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hsmall := mul_le_mul_of_nonneg_left hE (le_of_lt (inv_pos.mpr hr))
  rw [he] at hsmall
  have hI' : (∫ y : Space, ‖densityLinear w h y‖) ≤
      2 * M * ((∫ y : Space, |w y| ^ 4) + 1) * r := by
    calc
      _ ≤ (2 * M) * (r * (∫ y : Space, |w y| ^ 4) + r⁻¹ * (∫ y : Space, ‖h y‖ ^ 2)) := hI
      _ ≤ (2 * M) * (r * (∫ y : Space, |w y| ^ 4) + r) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hsmall) (by positivity)
      _ = _ := by ring
  have hb : ∀ᵐ y, ‖densityLinear w h y‖ ≤ 4 * M ^ 3 * r := by
    filter_upwards [hwb, hhb] with y hy hhy
    simp only [densityLinear, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy 3) (by norm_num))
      ((Complex.abs_re_le_norm (h y)).trans hhy) (abs_nonneg _) (by positivity)
  have hP := (potential_bound _ hi (4 * M ^ 3 * r) (by positivity) hb x).2
  calc
    _ ≤ nearMass * (4 * M ^ 3 * r) +
        2 * M * ((∫ y : Space, |w y| ^ 4) + 1) * r :=
      hP.trans (add_le_add le_rfl hI')
    _ = _ := by unfold linearPotentialConstant; ring

private theorem cubic_bounds (a : ℝ) (z : ℂ) {M r : ℝ}
    (hM : 0 ≤ M) (ha : |a| ≤ M) (hz : ‖z‖ ≤ r) :
    ‖cubicZero a‖ = |a| ^ 3 ∧
    ‖cubicLinear a z‖ ≤ 3 * M ^ 2 * ‖z‖ ∧
    ‖cubicRemainder a z‖ ≤ (3 * M + r) * r * ‖z‖ := by
  have hr : 0 ≤ r := (norm_nonneg z).trans hz
  have ha2 := pow_le_pow_left₀ (abs_nonneg a) ha 2
  have htwo : ‖(2 : ℂ) * (z.re : ℂ)‖ ≤ 2 * ‖z‖ := by
    calc
      _ = 2 * |z.re| := by norm_num [norm_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (by norm_num)
  have hsum : ‖2 * (z.re : ℂ) + z‖ ≤ 3 * ‖z‖ := by
    have ht := norm_add_le (2 * (z.re : ℂ)) z
    linarith
  have hlin : ‖cubicLinear a z‖ ≤ 3 * M ^ 2 * ‖z‖ := by
    calc
      _ = |a| ^ 2 * ‖2 * (z.re : ℂ) + z‖ := by simp [cubicLinear, norm_pow]
      _ ≤ M ^ 2 * (3 * ‖z‖) := mul_le_mul ha2 hsum (norm_nonneg _) (sq_nonneg M)
      _ = _ := by ring
  have hab : ‖(a : ℂ) + z‖ ≤ M + r := by
    have ht := norm_add_le (a : ℂ) z
    norm_num at ht
    linarith
  have ht1 : ‖(2 * (a : ℂ) * (z.re : ℂ)) * z‖ ≤ 2 * M * ‖z‖ ^ 2 := by
    calc
      _ = (2 * |a| * |z.re|) * ‖z‖ := by norm_num [norm_mul]
      _ ≤ (2 * M * ‖z‖) * ‖z‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
        exact mul_le_mul (by linarith : 2 * |a| ≤ 2 * M)
          (Complex.abs_re_le_norm z) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have ht2 : ‖((‖z‖ ^ 2 : ℝ) : ℂ) * ((a : ℂ) + z)‖ ≤ ‖z‖ ^ 2 * (M + r) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖z‖)]
    exact mul_le_mul_of_nonneg_left hab (sq_nonneg ‖z‖)
  have hrem : ‖cubicRemainder a z‖ ≤ (3 * M + r) * ‖z‖ ^ 2 := by
    have ht := norm_add_le ((2 * (a : ℂ) * (z.re : ℂ)) * z)
      (((‖z‖ ^ 2 : ℝ) : ℂ) * ((a : ℂ) + z))
    unfold cubicRemainder
    nlinarith only [ht, ht1, ht2]
  refine ⟨by simp [cubicZero, norm_pow], hlin, ?_⟩
  calc
    _ ≤ (3 * M + r) * ‖z‖ ^ 2 := hrem
    _ ≤ (3 * M + r) * (r * ‖z‖) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [mul_le_mul_of_nonneg_right hz (norm_nonneg z)]) (by positivity)
    _ = _ := by ring

private theorem product_sum_bound (P0 P1 PR c0 c1 cr : ℂ)
    {A0 A1 AR B0 B1 BR : ℝ}
    (hp0 : ‖P0‖ ≤ A0) (hp1 : ‖P1‖ ≤ A1) (hpR : ‖PR‖ ≤ AR)
    (hc0 : ‖c0‖ ≤ B0) (hc1 : ‖c1‖ ≤ B1) (hcr : ‖cr‖ ≤ BR) :
    ‖P0 * cr + P1 * (c1 + cr) + PR * (c0 + c1 + cr)‖ ≤
      A0 * BR + A1 * (B1 + BR) + AR * (B0 + B1 + BR) := by
  have h1 := (norm_add_le c1 cr).trans (add_le_add hc1 hcr)
  have h0 := (norm_add_le (c0 + c1) cr).trans
    (add_le_add ((norm_add_le c0 c1).trans (add_le_add hc0 hc1)) hcr)
  calc
    _ ≤ (‖P0 * cr‖ + ‖P1 * (c1 + cr)‖) + ‖PR * (c0 + c1 + cr)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (‖P0‖ * ‖cr‖ + ‖P1‖ * ‖c1 + cr‖) + ‖PR‖ * ‖c0 + c1 + cr‖ := by
      simp only [norm_mul]
    _ ≤ _ := add_le_add
      (add_le_add (mul_le_mul hp0 hcr (norm_nonneg _) ((norm_nonneg P0).trans hp0))
        (mul_le_mul hp1 h1 (norm_nonneg _) ((norm_nonneg P1).trans hp1)))
      (mul_le_mul hpR h0 (norm_nonneg _) ((norm_nonneg PR).trans hpR))

/-- Pointwise bound for the FULL remainder, including its W^3 nonlocal term. -/
theorem fullRemainder_pointwise_bound
    (κ : ℝ) (w : Space → ℝ) (h : Space → ℂ) (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4)) (hh : MemLp h 2)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r)
    (hE : (∫ y : Space, ‖h y‖ ^ 2) ≤ r ^ 2) :
    ∀ᵐ x, ‖remainder κ w h x‖ ≤ |κ| *
      (r * fullRemainderHConstant M r (∫ y : Space, |w y| ^ 4) * ‖h x‖ +
        quadraticPotentialConstant M r * r ^ 2 * |w x| ^ 3) := by
  filter_upwards [hwb, hhb] with x hx hxh
  have hc := cubic_bounds (w x) (h x) hM hx hxh
  have hp0 := background_potential_bound w hw4 hwb x
  have hp1 := densityLinear_potential_small w h hw hw4 hh hM hr hwb hhb hE x
  have hpR := densityRemainder_small_ball_bound w h hw hh hM hr.le hwb hhb hE x
  have hb := product_sum_bound _ _ _ _ _ _ hp0 hp1 hpR (le_of_eq hc.1) hc.2.1 hc.2.2
  unfold remainder
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |κ| * ((nearMass * M ^ 4 + ∫ y : Space, |w y| ^ 4) *
        ((3 * M + r) * r * ‖h x‖) +
      (linearPotentialConstant M (∫ y : Space, |w y| ^ 4) * r) *
        (3 * M ^ 2 * ‖h x‖ + (3 * M + r) * r * ‖h x‖) +
      (densityQuadraticConstant M r * (nearMass + 1) * r ^ 2) *
        (|w x| ^ 3 + 3 * M ^ 2 * ‖h x‖ + (3 * M + r) * r * ‖h x‖)) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg κ)
    _ = _ := by unfold fullRemainderHConstant quadraticPotentialConstant; ring

private theorem potential_aestrong (f : Space → ℂ) (hf : AEStronglyMeasurable f) :
    AEStronglyMeasurable (potential f) := by
  have hk : Measurable (fun p : Space × Space => (kernel (p.1 - p.2) : ℂ)) := by
    unfold kernel
    fun_prop
  have hm : AEStronglyMeasurable
      (fun p : Space × Space => (kernel (p.1 - p.2) : ℂ) * f p.2)
      ((volume : Measure Space).prod volume) :=
    hk.aestronglyMeasurable.mul hf.comp_snd
  exact hm.integral_prod_right'

private theorem remainder_aestrong (κ : ℝ) (w : Space → ℝ) (h : Space → ℂ)
    (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4)) (hh : MemLp h 2)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r) :
    AEStronglyMeasurable (remainder κ w h) := by
  have hwc := Complex.continuous_ofReal.comp_aestronglyMeasurable hw
  have hre := Complex.continuous_ofReal.comp_aestronglyMeasurable
    (Complex.continuous_re.comp_aestronglyMeasurable hh.aestronglyMeasurable)
  have hn := Complex.continuous_ofReal.comp_aestronglyMeasurable
    (hh.aestronglyMeasurable.norm.pow 2)
  have hc0 : AEStronglyMeasurable (fun x => cubicZero (w x)) := hwc.pow 3
  have hc1 : AEStronglyMeasurable (fun x => cubicLinear (w x) (h x)) :=
    (hwc.pow 2).mul ((hre.const_mul 2).add hh.aestronglyMeasurable)
  have hcr : AEStronglyMeasurable (fun x => cubicRemainder (w x) (h x)) :=
    (((hwc.const_mul 2).mul hre).mul hh.aestronglyMeasurable).add
      (hn.mul (hwc.add hh.aestronglyMeasurable))
  have hp0 := potential_aestrong _ (background_density_integrable w hw4).aestronglyMeasurable
  have hp1 := potential_aestrong _
    (densityLinear_source_integrable w h hw hw4 hh hM hr hwb hhb).1.aestronglyMeasurable
  have hpR := potential_aestrong _
    (densityRemainder_source_bound w h hw hh hM hr hwb hhb).1.aestronglyMeasurable
  exact (((hp0.mul hcr).add (hp1.mul (hc1.add hcr))).add
    (hpR.mul ((hc0.add hc1).add hcr))).const_mul (κ : ℂ)

/-- Quadratic L2 bound for the actual complete Taylor remainder.
No L2 assumption is placed on the background. -/
theorem fullRemainder_L2_bound
    (κ : ℝ) (w : Space → ℝ) (h : Space → ℂ) (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4)) (hh : MemLp h 2)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r)
    (hE : (∫ y : Space, ‖h y‖ ^ 2) ≤ r ^ 2) :
    let J := ∫ y : Space, |w y| ^ 4
    let A := fullRemainderHConstant M r J
    let B := quadraticPotentialConstant M r
    MemLp (remainder κ w h) 2 ∧
      (∫ x : Space, ‖remainder κ w h x‖ ^ 2) ≤
        2 * |κ| ^ 2 * (A ^ 2 + B ^ 2 * M ^ 2 * J) * r ^ 4 := by
  let J := ∫ y : Space, |w y| ^ 4
  let A := fullRemainderHConstant M r J
  let B := quadraticPotentialConstant M r
  have hm := remainder_aestrong κ w h hw hw4 hh hM hr.le hwb hhb
  have hpoint := fullRemainder_pointwise_bound κ w h hw hw4 hh hM hr hwb hhb hE
  have h6le : ∀ᵐ x, |w x| ^ 6 ≤ M ^ 2 * |w x| ^ 4 := by
    filter_upwards [hwb] with x hx
    calc
      _ = |w x| ^ 2 * |w x| ^ 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) hx 2) (by positivity)
  have hw6 : Integrable (fun x : Space => |w x| ^ 6) := by
    apply (hw4.const_mul (M ^ 2)).mono' (hw.norm.pow 6)
    filter_upwards [h6le] with x hx
    simpa only [Pi.pow_apply, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (abs_nonneg (w x)) 6)] using hx
  have hW6 := integral_mono_ae hw6 (hw4.const_mul (M ^ 2)) h6le
  rw [integral_const_mul] at hW6
  have hsq : ∀ᵐ x, ‖remainder κ w h x‖ ^ 2 ≤
      2 * |κ| ^ 2 * ((r * A) ^ 2 * ‖h x‖ ^ 2 + (B * r ^ 2) ^ 2 * |w x| ^ 6) := by
    filter_upwards [hpoint] with x hx
    have ht := pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hab : (r * A * ‖h x‖ + B * r ^ 2 * |w x| ^ 3) ^ 2 ≤
        2 * ((r * A * ‖h x‖) ^ 2 + (B * r ^ 2 * |w x| ^ 3) ^ 2) := by
      nlinarith only [sq_nonneg (r * A * ‖h x‖ - B * r ^ 2 * |w x| ^ 3)]
    calc
      _ ≤ |κ| ^ 2 * (r * A * ‖h x‖ + B * r ^ 2 * |w x| ^ 3) ^ 2 := by
        simpa only [mul_pow] using ht
      _ ≤ |κ| ^ 2 * (2 * ((r * A * ‖h x‖) ^ 2 + (B * r ^ 2 * |w x| ^ 3) ^ 2)) :=
        mul_le_mul_of_nonneg_left hab (sq_nonneg |κ|)
      _ = _ := by ring
  have hD := ((hh.norm.integrable_sq.const_mul ((r * A) ^ 2)).add
    (hw6.const_mul ((B * r ^ 2) ^ 2))).const_mul (2 * |κ| ^ 2)
  have hi2 : Integrable (fun x : Space => ‖remainder κ w h x‖ ^ 2) := by
    apply hD.mono' (hm.norm.pow 2)
    filter_upwards [hsq] with x hx
    simpa only [Pi.pow_apply, Pi.add_apply,
      Real.norm_of_nonneg (sq_nonneg ‖remainder κ w h x‖)] using hx
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).2 hi2, ?_⟩
  have hI := integral_mono_ae hi2 hD hsq
  simp only [Pi.add_apply] at hI
  rw [integral_const_mul,
    integral_add (hh.norm.integrable_sq.const_mul ((r * A) ^ 2))
      (hw6.const_mul ((B * r ^ 2) ^ 2)), integral_const_mul, integral_const_mul] at hI
  calc
    _ ≤ 2 * |κ| ^ 2 * ((r * A) ^ 2 * (∫ x : Space, ‖h x‖ ^ 2) +
        (B * r ^ 2) ^ 2 * (∫ x : Space, |w x| ^ 6)) := hI
    _ ≤ 2 * |κ| ^ 2 * ((r * A) ^ 2 * r ^ 2 + (B * r ^ 2) ^ 2 * (M ^ 2 * J)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hE (sq_nonneg _))
        (mul_le_mul_of_nonneg_left hW6 (sq_nonneg _))) (by positivity)
    _ = _ := by ring

/-- Quadratic essential-supremum bound for the same complete remainder. -/
theorem fullRemainder_Linfty_bound
    (κ : ℝ) (w : Space → ℝ) (h : Space → ℂ) (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4)) (hh : MemLp h 2)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r)
    (hE : (∫ y : Space, ‖h y‖ ^ 2) ≤ r ^ 2) :
    ∀ᵐ x, ‖remainder κ w h x‖ ≤ |κ| *
      (fullRemainderHConstant M r (∫ y : Space, |w y| ^ 4) +
        quadraticPotentialConstant M r * M ^ 3) * r ^ 2 := by
  have hJ : 0 ≤ ∫ y : Space, |w y| ^ 4 := integral_nonneg (fun _ => by positivity)
  have hc := constants_nonneg hM hr.le hJ
  have hp := fullRemainder_pointwise_bound κ w h hw hw4 hh hM hr hwb hhb hE
  filter_upwards [hp, hwb, hhb] with x hx hwx hhx
  calc
    _ ≤ |κ| * (r * fullRemainderHConstant M r (∫ y : Space, |w y| ^ 4) * ‖h x‖ +
        quadraticPotentialConstant M r * r ^ 2 * |w x| ^ 3) := hx
    _ ≤ |κ| * (r * fullRemainderHConstant M r (∫ y : Space, |w y| ^ 4) * r +
        quadraticPotentialConstant M r * r ^ 2 * M ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg κ)
      exact add_le_add
        (mul_le_mul_of_nonneg_left hhx (mul_nonneg hr.le hc.2.2))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hwx 3)
          (mul_nonneg hc.2.1 (sq_nonneg r)))
    _ = _ := by ring

end HBL.RegularRadiation.PhysicalExpansion
