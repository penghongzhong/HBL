import HBL.WeightedFreeGreenPointwise
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Injectivity of the actual weighted free Green operator.

The proof applies Lebesgue differentiation to the two absolutely continuous
primitives of an integrable source and its first moment. No continuity of
an arbitrary L2 input representative is assumed.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem minGreen_split_integrable
    {h : ℝ → ℝ} (hh : Integrable h)
    (hm : Integrable (fun r : ℝ => r * h r))
    {r : ℝ} (hr : 0 < r) :
    (∫ rho in Ioi (0 : ℝ), min r rho * h rho) =
      (∫ rho in (0 : ℝ)..r, rho * h rho) +
        r * ((∫ rho in Ioi (0 : ℝ), h rho) -
          ∫ rho in (0 : ℝ)..r, h rho) := by
  have hleft : IntegrableOn (fun rho : ℝ => min r rho * h rho)
      (Ioc (0 : ℝ) r) := by
    refine hm.integrableOn.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with rho hρ
    rw [min_eq_right hρ.2]
  have htail : IntegrableOn (fun rho : ℝ => min r rho * h rho)
      (Ioi r) := by
    refine (hh.integrableOn.const_mul r).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hρ
    change r * h rho = min r rho * h rho
    rw [min_eq_left hρ.le]
  have hsource : (∫ rho in Ioi (0 : ℝ), h rho) =
      (∫ rho in (0 : ℝ)..r, h rho) + ∫ rho in Ioi r, h rho := by
    rw [intervalIntegral.integral_of_le hr.le,
      ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        hh.integrableOn hh.integrableOn,
      Ioc_union_Ioi_eq_Ioi hr.le]
  rw [← Ioc_union_Ioi_eq_Ioi hr.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hleft htail]
  have hleft_eq : (∫ rho in Ioc (0 : ℝ) r, min r rho * h rho) =
      ∫ rho in (0 : ℝ)..r, rho * h rho := by
    rw [intervalIntegral.integral_of_le hr.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro rho hρ
    change min r rho * h rho = rho * h rho
    rw [min_eq_right hρ.2]
  have htail_eq : (∫ rho in Ioi r, min r rho * h rho) =
      r * ∫ rho in Ioi r, h rho := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro rho hρ
    change min r rho * h rho = r * h rho
    rw [min_eq_left hρ.le]
  rw [hleft_eq, htail_eq, Ioc_union_Ioi_eq_Ioi hr.le, hsource]
  ring

private theorem source_zero_of_minGreen_zero
    {h : ℝ → ℝ} (hh : Integrable h)
    (hm : Integrable (fun r : ℝ => r * h r))
    (hq : ∀ r : ℝ, 0 < r →
      (∫ rho in Ioi (0 : ℝ), min r rho * h rho) = 0) :
    h =ᵐ[halfLineMeasure] (0 : ℝ → ℝ) := by
  let A : ℝ → ℝ := fun r => ∫ rho in (0 : ℝ)..r, rho * h rho
  let B : ℝ → ℝ := fun r => ∫ rho in (0 : ℝ)..r, h rho
  let C : ℝ := ∫ rho in Ioi (0 : ℝ), h rho
  have hmodel_zero (r : ℝ) (hr : 0 < r) :
      A r + r * (C - B r) = 0 := by
    exact (minGreen_split_integrable hh hm hr).symm.trans (hq r hr)
  have hA := LocallyIntegrable.ae_hasDerivAt_integral hm.locallyIntegrable
  have hB := LocallyIntegrable.ae_hasDerivAt_integral hh.locallyIntegrable
  have htail_ae : (fun r : ℝ => C - B r) =ᵐ[halfLineMeasure]
      (0 : ℝ → ℝ) := by
    filter_upwards [ae_restrict_of_ae hA, ae_restrict_of_ae hB,
      ae_restrict_mem measurableSet_Ioi] with r hrA hrB hr
    have hmodel : HasDerivAt (fun x : ℝ => A x + x * (C - B x))
        (C - B r) r := by
      convert (hrA 0).add ((hasDerivAt_id r).mul
        ((hasDerivAt_const r C).sub (hrB 0))) using 1
      · rfl
      · simp only [id_eq, Pi.sub_apply, B]
        ring
    have hzero : HasDerivAt (fun x : ℝ => A x + x * (C - B x)) 0 r := by
      apply (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact hmodel_zero x hx
    exact hmodel.unique hzero
  have htail_cont : Continuous (fun r : ℝ => C - B r) :=
    continuous_const.sub (hh.continuous_primitive 0)
  have htail_zero : EqOn (fun r : ℝ => C - B r) (0 : ℝ → ℝ) (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq (μ := volume) htail_ae isOpen_Ioi
      htail_cont.continuousOn continuous_zero.continuousOn
  filter_upwards [ae_restrict_of_ae hB,
    ae_restrict_mem measurableSet_Ioi] with r hrB hr
  have htail : HasDerivAt (fun x : ℝ => C - B x) (-h r) r := by
    convert (hasDerivAt_const r C).sub (hrB 0) using 1
    simp
  have hzero : HasDerivAt (fun x : ℝ => C - B x) 0 r := by
    apply (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact htail_zero hx
  have hhzero := htail.unique hzero
  simpa using neg_eq_zero.mp hhzero

/-- The first moment of every weighted L2 source is integrable. -/
theorem weightedGreen_source_first_moment_integrable
    (f : RealL2 halfLineMeasure) :
    Integrable (fun r : ℝ => r * (weightedGreenDecay r * f r))
      halfLineMeasure := by
  have h := weightedGreenOutputMajorant_memLp_two.integrable_mul (Lp.memLp f)
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change weightedGreenOutputMajorant r * f r = r * (weightedGreenDecay r * f r)
  simp only [weightedGreenOutputMajorant, abs_of_pos (show 0 < r from hr)]
  ring

/-- A zero output of the actual Green operator forces its actual L2 input
to vanish. This statement has no source-regularity or spectral premises. -/
theorem weightedFreeGreenOperator_eq_zero_iff
    (f : RealL2 halfLineMeasure) :
    weightedFreeGreenOperator f = 0 ↔ f = 0 := by
  constructor
  · intro hzero
    have hp_ae : weightedFreeGreenPointwise f =ᵐ[halfLineMeasure]
        (0 : ℝ → ℝ) := by
      have hp := weightedFreeGreenOperator_ae_pointwise f
      rw [hzero] at hp
      exact hp.symm.trans (Lp.coeFn_zero ℝ 2 halfLineMeasure)
    have hp := Measure.eqOn_open_of_ae_eq (μ := volume) hp_ae isOpen_Ioi
      (weightedFreeGreenPointwise_continuous f).continuousOn
      continuous_zero.continuousOn
    have hq (r : ℝ) (hr : 0 < r) : weightedGreenPrimitive f r = 0 := by
      have hx := hp hr
      change weightedGreenDecay r * weightedGreenPrimitive f r = 0 at hx
      exact (mul_eq_zero.mp hx).resolve_left (by
        unfold weightedGreenDecay
        exact inv_ne_zero (by positivity))
    let h : ℝ → ℝ := (Ioi (0 : ℝ)).indicator
      (fun r : ℝ => weightedGreenDecay r * f r)
    have hh : Integrable h :=
      (show IntegrableOn (fun r : ℝ => weightedGreenDecay r * f r) (Ioi 0) volume
        from weightedGreen_source_integrable f).integrable_indicator measurableSet_Ioi
    have hm : Integrable (fun r : ℝ => r * h r) := by
      have hm0 := (show IntegrableOn
        (fun r : ℝ => r * (weightedGreenDecay r * f r)) (Ioi 0) volume
          from weightedGreen_source_first_moment_integrable f).integrable_indicator
            measurableSet_Ioi
      convert hm0 using 1
      funext r
      by_cases hr : r ∈ Ioi (0 : ℝ) <;> simp [h, hr]
    have hzero_source : h =ᵐ[halfLineMeasure] (0 : ℝ → ℝ) := by
      apply source_zero_of_minGreen_zero hh hm
      intro r hr
      calc
        (∫ rho in Ioi (0 : ℝ), min r rho * h rho) =
            weightedGreenPrimitive f r := by
          unfold weightedGreenPrimitive halfLineMeasure
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hρ
          simp [h, hρ]
        _ = 0 := hq r hr
    apply Lp.ext
    filter_upwards [hzero_source, Lp.coeFn_zero ℝ 2 halfLineMeasure,
      ae_restrict_mem measurableSet_Ioi] with r hr hL0 hpos
    rw [hL0]
    have hs : weightedGreenDecay r * f r = 0 := by simpa [h, hpos] using hr
    exact (mul_eq_zero.mp hs).resolve_left (by
      unfold weightedGreenDecay
      exact inv_ne_zero (by positivity))
  · rintro rfl
    exact map_zero _

/-- The actual weighted free Green operator is injective. -/
theorem weightedFreeGreenOperator_injective :
    Function.Injective weightedFreeGreenOperator := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply (weightedFreeGreenOperator_eq_zero_iff (f - g)).mp
  rw [map_sub, hfg, sub_self]

end HBL.Modulation.Monopole
