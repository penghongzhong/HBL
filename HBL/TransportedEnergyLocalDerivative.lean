import HBL.TransportedEnergyDual
import Mathlib.Analysis.Calculus.MeanValue

/-!
Local strong differentiation of the corrected transported energy tail.

The zero-scale derivative was already verified.  Here the same argument is
made uniform for every logarithmic scale a0 in (-1,1).  This is the
differentiability part of the C1 operator-norm statement needed by the
first manuscript modulation lemma.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace HBL.Modulation

/-- Pointwise scale differentiation of the corrected energy tail at any
interior logarithmic scale. -/
theorem transportedEnergyTail_hasDerivAt_of_mem
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a₀ : ℝ) (ha₀ : a₀ ∈ Ioo (-1 : ℝ) 1)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) :
    HasDerivAt (fun a : ℝ => transportedEnergyTail R zeta a s)
      (transportedEnergyTailScaleDerivative R zeta a₀ s) a₀ := by
  obtain ⟨C, hC0, hC⟩ :=
    transportedEnergyCoefficientDerivative_uniform_bound R zeta hzeta
  have hI : Icc (-1 : ℝ) 1 ∈ 𝓝 a₀ :=
    Icc_mem_nhds ha₀.1 ha₀.2
  have hFmeas :
      ∀ᶠ a in 𝓝 a₀,
        AEStronglyMeasurable
          (fun r : ℝ => transportedEnergyCoefficient zeta a r)
          ((volume : Measure ℝ).restrict (Ι s R)) := by
    apply Filter.Eventually.of_forall
    intro a
    have hz : Continuous zeta := hzeta.continuous
    have hc : Continuous (transportedEnergyCoefficient zeta a) := by
      change Continuous (fun r : ℝ =>
        Real.exp ((3 / 2 : ℝ) * a) * zeta (Real.exp a * r))
      fun_prop
    exact hc.aestronglyMeasurable
  have hF0int :
      IntervalIntegrable
        (transportedEnergyCoefficient zeta a₀) volume s R := by
    have hz : Continuous zeta := hzeta.continuous
    have hc : Continuous (transportedEnergyCoefficient zeta a₀) := by
      change Continuous (fun r : ℝ =>
        Real.exp ((3 / 2 : ℝ) * a₀) * zeta (Real.exp a₀ * r))
      fun_prop
    exact hc.intervalIntegrable (μ := volume) (a := s) (b := R)
  have hDcont :
      Continuous (transportedEnergyCoefficientDerivative zeta a₀) := by
    have hz : Continuous zeta := hzeta.continuous
    have hdz : Continuous (deriv zeta) := hzeta.continuous_deriv_one
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * a₀) *
        ((3 / 2 : ℝ) * zeta (Real.exp a₀ * r) +
          (Real.exp a₀ * r) * deriv zeta (Real.exp a₀ * r)))
    fun_prop
  have hDmeas :
      AEStronglyMeasurable
        (transportedEnergyCoefficientDerivative zeta a₀)
        ((volume : Measure ℝ).restrict (Ι s R)) :=
    hDcont.aestronglyMeasurable
  have hbound :
      ∀ᵐ r ∂(volume : Measure ℝ),
        r ∈ Ι s R →
        ∀ a ∈ Icc (-1 : ℝ) 1,
          ‖transportedEnergyCoefficientDerivative zeta a r‖ ≤ C := by
    apply Filter.Eventually.of_forall
    intro r hr a ha
    rw [uIoc_of_le hs.2] at hr
    exact hC a ha r ⟨hs.1.le.trans hr.1.le, hr.2⟩
  have hCint :
      IntervalIntegrable (fun _ : ℝ => C) volume s R :=
    continuous_const.intervalIntegrable (μ := volume) (a := s) (b := R)
  have hDiff :
      ∀ᵐ r ∂(volume : Measure ℝ),
        r ∈ Ι s R →
        ∀ a ∈ Icc (-1 : ℝ) 1,
          HasDerivAt
            (fun b : ℝ => transportedEnergyCoefficient zeta b r)
            (transportedEnergyCoefficientDerivative zeta a r) a :=
    Filter.Eventually.of_forall
      (fun r _ a _ =>
        transportedEnergyCoefficient_hasDerivAt zeta hzeta a r)
  have hcalc :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := s) (b := R)
      (F := fun a r => transportedEnergyCoefficient zeta a r)
      (F' := fun a r => transportedEnergyCoefficientDerivative zeta a r)
      (x₀ := a₀) (s := Icc (-1 : ℝ) 1)
      (bound := fun _ => C)
      hI hFmeas hF0int hDmeas hbound hCint hDiff
  change HasDerivAt
    (fun a : ℝ => transportedEnergyTail R zeta a s)
    (transportedEnergyTailScaleDerivative R zeta a₀ s) a₀
  exact hcalc.2

/-- Mean-value increment estimate for the corrected coefficient between two
arbitrary local logarithmic scales. -/
theorem transportedEnergyCoefficient_increment_bound_between
    (R C : ℝ) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hC : ∀ a ∈ Icc (-1 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) R,
      ‖transportedEnergyCoefficientDerivative zeta a r‖ ≤ C)
    (a b : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1)
    (hb : b ∈ Icc (-1 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
    ‖transportedEnergyCoefficient zeta a r -
        transportedEnergyCoefficient zeta b r‖ ≤ C * |a - b| := by
  have hder :
      ∀ x ∈ Icc (-1 : ℝ) 1,
        HasDerivWithinAt
          (fun y : ℝ => transportedEnergyCoefficient zeta y r)
          (transportedEnergyCoefficientDerivative zeta x r)
          (Icc (-1 : ℝ) 1) x := by
    intro x hx
    exact (transportedEnergyCoefficient_hasDerivAt
      zeta hzeta x r).hasDerivWithinAt
  have hmv :=
    (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      hder (fun x hx => hC x hx r hr) hb ha
  simpa [Real.norm_eq_abs] using hmv

/-- Uniform increment estimate for the corrected tail between two local
logarithmic scales. -/
theorem transportedEnergyTail_increment_bound_between
    (R C : ℝ) (hR : 0 ≤ R) (hC0 : 0 ≤ C)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hC : ∀ a ∈ Icc (-1 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) R,
      ‖transportedEnergyCoefficientDerivative zeta a r‖ ≤ C)
    (a b : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1)
    (hb : b ∈ Icc (-1 : ℝ) 1)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) :
    ‖transportedEnergyTail R zeta a s -
        transportedEnergyTail R zeta b s‖ ≤
      |a - b| * (C * R) := by
  have hz : Continuous zeta := hzeta.continuous
  have hCa : Continuous (transportedEnergyCoefficient zeta a) := by
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * a) * zeta (Real.exp a * r))
    fun_prop
  have hCb : Continuous (transportedEnergyCoefficient zeta b) := by
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * b) * zeta (Real.exp b * r))
    fun_prop
  have hia : IntervalIntegrable
      (transportedEnergyCoefficient zeta a) volume s R :=
    hCa.intervalIntegrable (μ := volume) (a := s) (b := R)
  have hib : IntervalIntegrable
      (transportedEnergyCoefficient zeta b) volume s R :=
    hCb.intervalIntegrable (μ := volume) (a := s) (b := R)
  have heq :
      transportedEnergyTail R zeta a s -
          transportedEnergyTail R zeta b s =
        ∫ r in s..R,
          (transportedEnergyCoefficient zeta a r -
            transportedEnergyCoefficient zeta b r) := by
    unfold transportedEnergyTail
    rw [intervalIntegral.integral_sub hia hib]
  rw [heq]
  have hpoint :
      ∀ r ∈ Ι s R,
        ‖transportedEnergyCoefficient zeta a r -
            transportedEnergyCoefficient zeta b r‖ ≤ C * |a - b| := by
    intro r hr
    rw [uIoc_of_le hs.2] at hr
    exact transportedEnergyCoefficient_increment_bound_between
      R C zeta hzeta hC a b ha hb r
      ⟨hs.1.le.trans hr.1.le, hr.2⟩
  have hint :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun r =>
        transportedEnergyCoefficient zeta a r -
          transportedEnergyCoefficient zeta b r)
      hpoint
  rw [abs_of_nonneg (sub_nonneg.mpr hs.2)] at hint
  calc
    ‖∫ r in s..R,
        (transportedEnergyCoefficient zeta a r -
          transportedEnergyCoefficient zeta b r)‖
        ≤ (C * |a - b|) * (R - s) := hint
    _ = |a - b| * (C * (R - s)) := by ring
    _ ≤ |a - b| * (C * R) := by
      gcongr
      nlinarith [hs.1.le]

/-- Strong L2 derivative of the corrected transported representer at every
interior logarithmic scale. -/
theorem transportedEnergyTailL2_hasDerivAt_of_mem
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a₀ : ℝ) (ha₀ : a₀ ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt
      (transportedEnergyTailL2 R hR zeta hzeta)
      (transportedEnergyTailScaleDerivativeL2
        R hR zeta hzeta a₀) a₀ := by
  obtain ⟨C, hC0, hC⟩ :=
    transportedEnergyCoefficientDerivative_uniform_bound R zeta hzeta
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) R)
  let F : ℝ → ℝ → ℝ := fun a s => transportedEnergyTail R zeta a s
  let g : ℝ → ℝ := transportedEnergyTailScaleDerivative R zeta a₀
  have hF (a : ℝ) : MemLp (F a) 2 μ := by
    dsimp [F, μ]
    exact continuous_memLp_restrict_Ioc 0 R hR
      (transportedEnergyTail R zeta a)
      (transportedEnergyTail_contDiff_one_in_s
        R zeta hzeta a).continuous 2
  have hg : MemLp g 2 μ := by
    dsimp [g, μ]
    exact continuous_memLp_restrict_Ioc 0 R hR
      (transportedEnergyTailScaleDerivative R zeta a₀)
      (transportedEnergyTailScaleDerivative_contDiff_one
        R zeta hzeta a₀).continuous 2
  have hw :
      Integrable (fun _ : ℝ => (C * R) ^ 2) μ := by
    dsimp [μ]
    exact (continuous_const :
      Continuous (fun _ : ℝ => (C * R) ^ 2)).integrableOn_Ioc
  have hI : Icc (-1 : ℝ) 1 ∈ 𝓝 a₀ :=
    Icc_mem_nhds ha₀.1 ha₀.2
  have ha₀cc : a₀ ∈ Icc (-1 : ℝ) 1 := ⟨ha₀.1.le, ha₀.2.le⟩
  have hinc :
      ∀ᶠ a in 𝓝 a₀,
        ∀ᵐ s ∂μ,
          ‖F a s - F a₀ s‖ ≤ |a - a₀| * (C * R) := by
    filter_upwards [hI] with a ha
    dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp [F]
    exact transportedEnergyTail_increment_bound_between
      R C hR hC0 zeta hzeta hC a a₀ ha ha₀cc s hs
  have hgb :
      ∀ᵐ s ∂μ, ‖g s‖ ≤ C * R := by
    dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have ht := transportedEnergyTailScaleDerivative_abs_le
      R C zeta a₀ s hs
      (fun r hr => hC a₀ ha₀cc r hr)
    dsimp [g]
    exact ht.trans (by
      gcongr
      nlinarith [hs.1.le])
  have hd :
      ∀ᵐ s ∂μ,
        HasDerivAt (fun a => F a s) (g s) a₀ := by
    dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp [F, g]
    exact transportedEnergyTail_hasDerivAt_of_mem
      R hR zeta hzeta a₀ ha₀ s hs
  have hstrong :=
    realLp2_hasDerivAt_of_increment_bound
      (μ := μ) F g a₀ hF hg (fun _ => C * R)
      hw hinc hgb hd
  change HasDerivAt
    (transportedEnergyTailL2 R hR zeta hzeta)
    (transportedEnergyTailScaleDerivativeL2
      R hR zeta hzeta a₀) a₀
  convert hstrong using 1
  · funext a
    dsimp [F, μ]
    unfold transportedEnergyTailL2
    apply MemLp.toLp_congr
    exact Filter.EventuallyEq.rfl
  · dsimp [g, μ]
    unfold transportedEnergyTailScaleDerivativeL2
    apply MemLp.toLp_congr
    exact Filter.EventuallyEq.rfl

end HBL.Modulation
