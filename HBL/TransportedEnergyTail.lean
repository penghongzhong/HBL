import HBL.TransportedEnergyCoefficient
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Differentiation of the corrected transported energy tail.

The correct energy-coordinate coefficient is
  C_a(r) = exp(3a/2) * zeta(exp(a) r),
and its tail is
  Q_a(s) = integral_s^R C_a(r) dr.

This module verifies the joint continuity and compact uniform bounds of
the coefficient derivative, differentiates Q_a pointwise at a=0, and
bundles the candidate derivative as a classical continuous function of s.
The strong L2 derivative is handled in the next module.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace HBL.Modulation

/-- Joint continuity of the corrected coefficient derivative. -/
theorem transportedEnergyCoefficientDerivative_joint_continuous
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    Continuous (fun p : ℝ × ℝ =>
      transportedEnergyCoefficientDerivative zeta p.1 p.2) := by
  have hz : Continuous zeta := hzeta.continuous
  have hdz : Continuous (deriv zeta) := hzeta.continuous_deriv_one
  dsimp [transportedEnergyCoefficientDerivative]
  fun_prop

/-- Uniform bound for the corrected coefficient derivative on the local
scale-radius rectangle. -/
theorem transportedEnergyCoefficientDerivative_uniform_bound
    (R : ℝ) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Icc (-1 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) R,
        ‖transportedEnergyCoefficientDerivative zeta a r‖ ≤ C := by
  have hcont :=
    transportedEnergyCoefficientDerivative_joint_continuous zeta hzeta
  have hcompact :
      IsCompact ((Icc (-1 : ℝ) 1) ×ˢ (Icc (0 : ℝ) R)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, hC₀⟩ :=
    hcompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro a ha r hr
  exact (hC₀ (a, r) ⟨ha, hr⟩).trans (le_max_left _ _)

/-- Tail of the corrected coefficient derivative. -/
def transportedEnergyTailScaleDerivative
    (R : ℝ) (zeta : ℝ → ℝ) (a s : ℝ) : ℝ :=
  ∫ r in s..R, transportedEnergyCoefficientDerivative zeta a r

/-- The derivative tail is C1 in the radial endpoint. -/
theorem transportedEnergyTailScaleDerivative_contDiff_one
    (R : ℝ) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    ContDiff ℝ 1 (transportedEnergyTailScaleDerivative R zeta a) := by
  have hz : Continuous zeta := hzeta.continuous
  have hdz : Continuous (deriv zeta) := hzeta.continuous_deriv_one
  have hD : Continuous (transportedEnergyCoefficientDerivative zeta a) := by
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * a) *
        ((3 / 2 : ℝ) * zeta (Real.exp a * r) +
          (Real.exp a * r) * deriv zeta (Real.exp a * r)))
    fun_prop
  change ContDiff ℝ 1
    (fun s : ℝ =>
      ∫ r in s..R, transportedEnergyCoefficientDerivative zeta a r)
  exact testTailPrimitive_contDiff_one R
    (transportedEnergyCoefficientDerivative zeta a) hD

/-- The corrected transported energy tail is C1 in the radial endpoint. -/
theorem transportedEnergyTail_contDiff_one_in_s
    (R : ℝ) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    ContDiff ℝ 1 (transportedEnergyTail R zeta a) := by
  have hz : Continuous zeta := hzeta.continuous
  have hC : Continuous (transportedEnergyCoefficient zeta a) := by
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * a) * zeta (Real.exp a * r))
    fun_prop
  change ContDiff ℝ 1
    (fun s : ℝ =>
      ∫ r in s..R, transportedEnergyCoefficient zeta a r)
  exact testTailPrimitive_contDiff_one R
    (transportedEnergyCoefficient zeta a) hC

/-- Pointwise scale derivative at a=0 for the corrected energy tail. -/
theorem transportedEnergyTail_hasDerivAt_zero
    (R s : ℝ) (hR : 0 ≤ R) (hs : s ∈ Ioc (0 : ℝ) R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    HasDerivAt (fun a : ℝ => transportedEnergyTail R zeta a s)
      (transportedEnergyTailScaleDerivative R zeta 0 s) 0 := by
  obtain ⟨C, hC0, hC⟩ :=
    transportedEnergyCoefficientDerivative_uniform_bound R zeta hzeta
  have hI : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hFmeas :
      ∀ᶠ a in 𝓝 (0 : ℝ),
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
        (transportedEnergyCoefficient zeta 0) volume s R := by
    have hz : Continuous zeta := hzeta.continuous
    have hc : Continuous (transportedEnergyCoefficient zeta 0) := by
      change Continuous (fun r : ℝ =>
        Real.exp ((3 / 2 : ℝ) * 0) * zeta (Real.exp 0 * r))
      fun_prop
    exact hc.intervalIntegrable (μ := volume) (a := s) (b := R)
  have hDcont :
      Continuous (transportedEnergyCoefficientDerivative zeta 0) := by
    have hz : Continuous zeta := hzeta.continuous
    have hdz : Continuous (deriv zeta) := hzeta.continuous_deriv_one
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * 0) *
        ((3 / 2 : ℝ) * zeta (Real.exp 0 * r) +
          (Real.exp 0 * r) * deriv zeta (Real.exp 0 * r)))
    fun_prop
  have hDmeas :
      AEStronglyMeasurable
        (transportedEnergyCoefficientDerivative zeta 0)
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
      (x₀ := (0 : ℝ)) (s := Icc (-1 : ℝ) 1)
      (bound := fun _ => C)
      hI hFmeas hF0int hDmeas hbound hCint hDiff
  change HasDerivAt
    (fun a : ℝ => transportedEnergyTail R zeta a s)
    (transportedEnergyTailScaleDerivative R zeta 0 s) 0
  exact hcalc.2

/-- Uniform pointwise bound on the corrected derivative tail. -/
theorem transportedEnergyTailScaleDerivative_abs_le
    (R C : ℝ) (zeta : ℝ → ℝ) (a s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) R)
    (hC : ∀ r ∈ Icc (0 : ℝ) R,
      ‖transportedEnergyCoefficientDerivative zeta a r‖ ≤ C) :
    ‖transportedEnergyTailScaleDerivative R zeta a s‖ ≤
      C * (R - s) := by
  have hb :
      ∀ r ∈ Ι s R,
        ‖transportedEnergyCoefficientDerivative zeta a r‖ ≤ C := by
    intro r hr
    rw [uIoc_of_le hs.2] at hr
    exact hC r ⟨hs.1.le.trans hr.1.le, hr.2⟩
  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := transportedEnergyCoefficientDerivative zeta a) hb
  simpa [transportedEnergyTailScaleDerivative,
    abs_of_nonneg (sub_nonneg.mpr hs.2)] using h

end HBL.Modulation
