import HBL.AffineTailPlusGreen
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space

/-!
Closure of the manuscript's second numbered environment: the affine-tail
threshold charge for both Hartree channels and weighted `L²` data.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.AffineTail

/-- Complete imaginary-channel affine charge density. -/
def hMinusAffineDensity (r : ℝ) : ℝ :=
  resonanceMinus r * hMinusApply model r

theorem resonanceMinus_abs_le_one (r : ℝ) (hr : 0 ≤ r) :
    |resonanceMinus r| ≤ 1 := by
  rw [resonanceMinus_def]
  unfold bubble
  rw [abs_mul, abs_inv, abs_of_nonneg hr,
    abs_of_pos (by positivity : 0 < Real.sqrt (1 + r ^ 2))]
  have hrle : r ≤ Real.sqrt (1 + r ^ 2) := by
    rw [Real.le_sqrt hr (by positivity)]
    nlinarith [sq_nonneg r]
  rw [← div_eq_mul_inv, div_le_one (by positivity :
    0 < Real.sqrt (1 + r ^ 2))]
  exact hrle

theorem hMinusAffineDensity_continuous :
    Continuous hMinusAffineDensity := by
  have hq : ContDiff ℝ ∞ model := model_contDiff_infty
  have hq1 : ContDiff ℝ ∞ (deriv model) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hq2 : ContDiff ℝ ∞ (deriv (deriv model)) :=
    (contDiff_infty_iff_deriv.mp hq1).2
  unfold hMinusAffineDensity hMinusApply
  exact radialResonanceMinus_contDiff_infty.continuous.mul
    (hq2.continuous.neg.sub (potential_continuous.mul hq.continuous))

theorem hMinusAffineDensity_far (r : ℝ) (hr : 2 < r) :
    hMinusAffineDensity r =
      -resonanceMinus r * potential r * r := by
  unfold hMinusAffineDensity hMinusApply
  rw [model_second_deriv_eq_zero_of_two_lt r hr,
    model_eq_id_of_two_le r hr.le]
  ring

theorem hMinusAffineDensity_norm_far_le
    (r : ℝ) (hr : 2 < r) :
    ‖hMinusAffineDensity r‖ ≤
      3 * (1 + r ^ 2)⁻¹ := by
  rw [hMinusAffineDensity_far r hr, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (show 0 ≤ r by linarith),
    abs_of_nonneg (show 0 ≤ potential r by unfold potential; positivity)]
  have hpsi := resonanceMinus_abs_le_one r (by linarith)
  have hrle : r ≤ 1 + r ^ 2 := by
    nlinarith [sq_nonneg (r - 1)]
  unfold potential
  rw [div_eq_mul_inv]
  have htail : r * ((1 + r ^ 2) ^ 2)⁻¹ ≤ (1 + r ^ 2)⁻¹ := by
    rw [← inv_pow]
    calc
      r * ((1 + r ^ 2)⁻¹) ^ 2 ≤
          (1 + r ^ 2) * ((1 + r ^ 2)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right hrle (sq_nonneg _)
      _ = (1 + r ^ 2)⁻¹ := by field_simp
  have hprod : |resonanceMinus r| *
      (r * ((1 + r ^ 2) ^ 2)⁻¹) ≤ (1 + r ^ 2)⁻¹ := by
    simpa only [one_mul] using
      (mul_le_mul hpsi htail
        (mul_nonneg (by linarith) (inv_nonneg.mpr (sq_nonneg _)))
        zero_le_one)
  calc
    |resonanceMinus r| *
        (3 * ((1 + r ^ 2) ^ 2)⁻¹) * r =
        3 * (|resonanceMinus r| *
          (r * ((1 + r ^ 2) ^ 2)⁻¹)) := by ring
    _ ≤ 3 * (1 + r ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)

theorem hMinusAffineDensity_integrableOn :
    IntegrableOn hMinusAffineDensity (Ioi (0 : ℝ)) := by
  have hcompact : IntegrableOn hMinusAffineDensity (Ioc (0 : ℝ) 2) :=
    (hMinusAffineDensity_continuous.continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hmajor : IntegrableOn
      (fun r : ℝ => 3 * (1 + r ^ 2)⁻¹) (Ioi 2) :=
    (integrable_inv_one_add_sq.const_mul 3).integrableOn
  have htail : IntegrableOn hMinusAffineDensity (Ioi 2) := by
    refine hmajor.mono'
      hMinusAffineDensity_continuous.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hMinusAffineDensity_norm_far_le r hr
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 by norm_num)]
  exact hcompact.union htail

theorem hMinus_affine_pairing_eq_neg_one :
    (∫ r in Ioi (0 : ℝ),
      resonanceMinus r * hMinusApply model r) = -1 := by
  have hIntegral := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    hMinusAffineDensity_integrableOn tendsto_id
  change Tendsto
    (fun R : ℝ => ∫ r in (0 : ℝ)..R,
      resonanceMinus r * hMinusApply model r)
    atTop (𝓝 (∫ r in Ioi (0 : ℝ),
      resonanceMinus r * hMinusApply model r)) at hIntegral
  exact tendsto_nhds_unique hIntegral hMinus_charge_interval_tendsto_neg_one

/-- The two scalar Hartree channels occurring in the affine-charge lemma. -/
inductive HartreeChannel
  | minus
  | plus
  deriving DecidableEq

def channelResonance : HartreeChannel → ℝ → ℝ
  | .minus => resonanceMinus
  | .plus => resonancePlus

def channelApply : HartreeChannel → (ℝ → ℝ) → ℝ → ℝ
  | .minus => hMinusApply
  | .plus => hPlusApply

/-- The nonzero far-field resonance constant. -/
def channelLimit : HartreeChannel → ℝ
  | .minus => 1
  | .plus => -(1 / 2)

theorem channelLimit_ne_zero (ch : HartreeChannel) :
    channelLimit ch ≠ 0 := by
  cases ch <;> norm_num [channelLimit]

theorem channelResonance_continuous (ch : HartreeChannel) :
    Continuous (channelResonance ch) := by
  cases ch
  · exact radialResonanceMinus_contDiff_infty.continuous
  · exact resonancePlus_contDiff_infty.continuous

theorem channelResonance_abs_le_one
    (ch : HartreeChannel) (r : ℝ) (hr : 0 ≤ r) :
    |channelResonance ch r| ≤ 1 := by
  cases ch
  · exact resonanceMinus_abs_le_one r hr
  · exact (resonancePlus_abs_le_half r hr).trans (by norm_num)

/-- The manuscript Japanese-bracket weight `⟨r⟩^σ`. -/
def affineJapaneseWeight (sigma r : ℝ) : ℝ :=
  (1 + r ^ 2) ^ (sigma / 2)

/-- Its reciprocal power, used in weighted Cauchy--Schwarz. -/
def affineJapaneseDecay (sigma r : ℝ) : ℝ :=
  (1 + r ^ 2) ^ (-sigma / 2)

theorem affineJapaneseDecay_continuous (sigma : ℝ) :
    Continuous (affineJapaneseDecay sigma) := by
  unfold affineJapaneseDecay
  have hb : Continuous (fun r : ℝ => 1 + r ^ 2) := by fun_prop
  exact hb.rpow_const (fun r => Or.inl (by positivity))

/-- Exact function-level definition of `L^{2,σ}(0,∞)`. -/
def InWeightedL2 (sigma : ℝ) (F : ℝ → ℝ) : Prop :=
  MemLp (fun r => affineJapaneseWeight sigma r * F r) 2
    (volume.restrict (Ioi (0 : ℝ)))

theorem affineJapaneseDecay_sq (sigma r : ℝ) :
    affineJapaneseDecay sigma r ^ 2 =
      (1 + r ^ 2) ^ (-sigma) := by
  unfold affineJapaneseDecay
  rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem affineJapaneseDecay_memLp_two
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    MemLp (affineJapaneseDecay sigma) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 * sigma := by
    rw [Module.finrank_self]
    norm_num
    linarith
  have hfull : Integrable (fun r : ℝ =>
      (1 + r ^ 2) ^ (-sigma)) := by
    have h := integrable_rpow_neg_one_add_norm_sq
      (E := ℝ) (μ := volume) hdim
    simp only [Real.norm_eq_abs, sq_abs] at h
    refine h.congr (Filter.Eventually.of_forall fun r => ?_)
    ring_nf
  have hmemFull : MemLp (affineJapaneseDecay sigma) 2 volume := by
    apply (memLp_two_iff_integrable_sq
      (affineJapaneseDecay_continuous sigma).aestronglyMeasurable).2
    simpa only [affineJapaneseDecay_sq] using hfull
  exact hmemFull.mono_measure Measure.restrict_le_self

theorem channelResonance_decay_memLp_two
    (ch : HartreeChannel) (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    MemLp (fun r => channelResonance ch r *
      affineJapaneseDecay sigma r) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  refine (affineJapaneseDecay_memLp_two sigma hsigma).mono'
    ((channelResonance_continuous ch).mul
      (affineJapaneseDecay_continuous sigma)).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (show 0 ≤ affineJapaneseDecay sigma r by
      unfold affineJapaneseDecay; positivity)]
  exact mul_le_of_le_one_left
    (by unfold affineJapaneseDecay; positivity)
    (channelResonance_abs_le_one ch r hr.le)

theorem affineJapaneseDecay_mul_weight (sigma r : ℝ) :
    affineJapaneseDecay sigma r * affineJapaneseWeight sigma r = 1 := by
  unfold affineJapaneseDecay affineJapaneseWeight
  rw [← Real.rpow_add (by positivity)]
  convert Real.rpow_zero (1 + r ^ 2) using 2
  ring

theorem channel_data_pairing_integrableOn
    (ch : HartreeChannel) (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    IntegrableOn (fun r => channelResonance ch r * F r) (Ioi 0) := by
  have hprod := (channelResonance_decay_memLp_two ch sigma hsigma).integrable_mul hF
  refine hprod.congr ?_
  filter_upwards with r
  simp only [Pi.mul_apply]
  rw [show
    (channelResonance ch r * affineJapaneseDecay sigma r) *
        (affineJapaneseWeight sigma r * F r) =
      channelResonance ch r *
        (affineJapaneseDecay sigma r * affineJapaneseWeight sigma r) * F r by
        ring,
    affineJapaneseDecay_mul_weight, mul_one]

/-- The actual source `H(χ_aff r)` in either channel. -/
def channelAffineSource (ch : HartreeChannel) : ℝ → ℝ :=
  channelApply ch model

theorem channel_affine_density_integrableOn (ch : HartreeChannel) :
    IntegrableOn (fun r =>
      channelResonance ch r * channelAffineSource ch r) (Ioi 0) := by
  cases ch
  · exact hMinusAffineDensity_integrableOn
  · exact hPlusAffineDensity_integrableOn

/-- Pairing with the explicit zero-energy resonance. -/
def channelPairing (ch : HartreeChannel) (F : ℝ → ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), channelResonance ch r * F r

theorem channel_affine_pairing_eq_neg_limit (ch : HartreeChannel) :
    channelPairing ch (channelAffineSource ch) = -channelLimit ch := by
  cases ch
  · exact hMinus_affine_pairing_eq_neg_one
  · simpa [channelPairing, channelAffineSource, channelApply,
      channelResonance, channelLimit] using hPlus_affine_pairing_eq_half

/-- The precise orthogonality assertion appearing in the manuscript. -/
def AffineTailOrthogonal
    (ch : HartreeChannel) (F₀ : ℝ → ℝ) (alpha : ℝ) : Prop :=
  IntegrableOn (fun r => channelResonance ch r *
      (F₀ r - alpha * channelAffineSource ch r)) (Ioi 0) ∧
    channelPairing ch
      (fun r => F₀ r - alpha * channelAffineSource ch r) = 0

theorem channel_corrected_integrableOn
    (ch : HartreeChannel) (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F₀ : ℝ → ℝ) (hF₀ : InWeightedL2 sigma F₀) (alpha : ℝ) :
    IntegrableOn (fun r => channelResonance ch r *
      (F₀ r - alpha * channelAffineSource ch r)) (Ioi 0) := by
  have hF := channel_data_pairing_integrableOn ch sigma hsigma F₀ hF₀
  have hq := (channel_affine_density_integrableOn ch).const_mul alpha
  have h := hF.sub hq
  refine h.congr_fun ?_ measurableSet_Ioi
  intro r _
  simp only [Pi.sub_apply]
  ring

theorem channel_corrected_pairing_eq
    (ch : HartreeChannel) (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F₀ : ℝ → ℝ) (hF₀ : InWeightedL2 sigma F₀) (alpha : ℝ) :
    channelPairing ch
        (fun r => F₀ r - alpha * channelAffineSource ch r) =
      channelPairing ch F₀ + alpha * channelLimit ch := by
  have hF := channel_data_pairing_integrableOn ch sigma hsigma F₀ hF₀
  have hq := channel_affine_density_integrableOn ch
  have hqValue := channel_affine_pairing_eq_neg_limit ch
  unfold channelPairing at hqValue
  unfold channelPairing
  have heq :
      (∫ r in Ioi (0 : ℝ), channelResonance ch r *
        (F₀ r - alpha * channelAffineSource ch r)) =
      ∫ r in Ioi (0 : ℝ),
        channelResonance ch r * F₀ r -
          alpha * (channelResonance ch r * channelAffineSource ch r) := by
    apply integral_congr_ae
    filter_upwards with r
    ring
  rw [heq, integral_sub hF (hq.const_mul alpha), integral_const_mul,
    hqValue]
  ring

theorem affineTailOrthogonal_iff_charge_formula
    (ch : HartreeChannel) (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F₀ : ℝ → ℝ) (hF₀ : InWeightedL2 sigma F₀) (alpha : ℝ) :
    AffineTailOrthogonal ch F₀ alpha ↔
      alpha = -(channelPairing ch F₀) / channelLimit ch := by
  constructor
  · intro h
    have hz := h.2
    rw [channel_corrected_pairing_eq ch sigma hsigma F₀ hF₀ alpha] at hz
    apply (eq_div_iff (channelLimit_ne_zero ch)).2
    linarith
  · intro halpha
    refine ⟨channel_corrected_integrableOn ch sigma hsigma F₀ hF₀ alpha, ?_⟩
    rw [channel_corrected_pairing_eq ch sigma hsigma F₀ hF₀ alpha,
      halpha]
    field_simp [channelLimit_ne_zero ch]
    ring

/-- **Second manuscript theorem environment, fully closed.**
For `3/2 < σ < 2`, every `F₀ ∈ L^{2,σ}` has one and only one affine
threshold charge, and it is exactly `-⟨ψ,F₀⟩/c` in both channels. -/
theorem secondManuscriptAffineTailEnvironment_closed
    (sigma : ℝ) (hsigmaLower : 3 / 2 < sigma) (hsigmaUpper : sigma < 2)
    (ch : HartreeChannel) (F₀ : ℝ → ℝ) (hF₀ : InWeightedL2 sigma F₀) :
    (∃! alpha : ℝ, AffineTailOrthogonal ch F₀ alpha) ∧
      (∀ alpha : ℝ, AffineTailOrthogonal ch F₀ alpha ↔
        alpha = -(channelPairing ch F₀) / channelLimit ch) := by
  have hsigma : 1 / 2 < sigma := by linarith
  have hformula := affineTailOrthogonal_iff_charge_formula
    ch sigma hsigma F₀ hF₀
  constructor
  · refine ⟨-(channelPairing ch F₀) / channelLimit ch,
      (hformula _).2 rfl, ?_⟩
    intro alpha halpha
    exact (hformula alpha).1 halpha
  · exact hformula

end HBL.Modulation.AffineTail
