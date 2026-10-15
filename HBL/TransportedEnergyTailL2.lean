import HBL.TransportedEnergyTail
import HBL.L2DominatedDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-!
Strong L2 differentiation of the corrected transported energy tail.

The correct dual representer is the tail of
  C_a(r) = exp(3a/2) zeta(exp(a) r),
not the tail of C_a(r) r.  This module bundles the correct tail and its
scale derivative in the finite-radius radial energy Hilbert space and
upgrades the verified pointwise derivative to a strong L2 derivative.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace HBL.Modulation

/-- Correct transported dual representer as a vector of the finite-radius
radial energy Hilbert space. -/
def transportedEnergyTailL2
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    RadialEnergyL2 R :=
  (continuous_memLp_restrict_Ioc 0 R hR
    (transportedEnergyTail R zeta a)
    (transportedEnergyTail_contDiff_one_in_s R zeta hzeta a).continuous 2).toLp
      (transportedEnergyTail R zeta a)

/-- Almost-everywhere identification of the corrected L2 representer. -/
theorem transportedEnergyTailL2_ae
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    (transportedEnergyTailL2 R hR zeta hzeta a : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) R)]
      transportedEnergyTail R zeta a := by
  exact (continuous_memLp_restrict_Ioc 0 R hR
    (transportedEnergyTail R zeta a)
    (transportedEnergyTail_contDiff_one_in_s R zeta hzeta a).continuous 2).coeFn_toLp

/-- Correct candidate scale derivative as an L2 vector. -/
def transportedEnergyTailScaleDerivativeL2
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    RadialEnergyL2 R :=
  (continuous_memLp_restrict_Ioc 0 R hR
    (transportedEnergyTailScaleDerivative R zeta a)
    (transportedEnergyTailScaleDerivative_contDiff_one
      R zeta hzeta a).continuous 2).toLp
      (transportedEnergyTailScaleDerivative R zeta a)

/-- Almost-everywhere identification of the candidate L2 derivative. -/
theorem transportedEnergyTailScaleDerivativeL2_ae
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    (transportedEnergyTailScaleDerivativeL2
      R hR zeta hzeta a : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) R)]
      transportedEnergyTailScaleDerivative R zeta a := by
  exact (continuous_memLp_restrict_Ioc 0 R hR
    (transportedEnergyTailScaleDerivative R zeta a)
    (transportedEnergyTailScaleDerivative_contDiff_one
      R zeta hzeta a).continuous 2).coeFn_toLp

/-- Mean-value increment estimate for the corrected coefficient. -/
theorem transportedEnergyCoefficient_increment_bound
    (R C : ℝ) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hC : ∀ a ∈ Icc (-1 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) R,
      ‖transportedEnergyCoefficientDerivative zeta a r‖ ≤ C)
    (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
    ‖transportedEnergyCoefficient zeta a r -
        transportedEnergyCoefficient zeta 0 r‖ ≤ C * |a| := by
  have hder :
      ∀ b ∈ Icc (-1 : ℝ) 1,
        HasDerivWithinAt
          (fun x : ℝ => transportedEnergyCoefficient zeta x r)
          (transportedEnergyCoefficientDerivative zeta b r)
          (Icc (-1 : ℝ) 1) b := by
    intro b hb
    exact (transportedEnergyCoefficient_hasDerivAt
      zeta hzeta b r).hasDerivWithinAt
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hmv :=
    (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      hder (fun b hb => hC b hb r hr) h0 ha
  simpa [Real.norm_eq_abs] using hmv

/-- Uniform increment bound for the corrected energy tail. -/
theorem transportedEnergyTail_increment_bound
    (R C : ℝ) (hR : 0 ≤ R) (hC0 : 0 ≤ C)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hC : ∀ a ∈ Icc (-1 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) R,
      ‖transportedEnergyCoefficientDerivative zeta a r‖ ≤ C)
    (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) :
    ‖transportedEnergyTail R zeta a s -
        transportedEnergyTail R zeta 0 s‖ ≤ |a| * (C * R) := by
  have hz : Continuous zeta := hzeta.continuous
  have hCa : Continuous (transportedEnergyCoefficient zeta a) := by
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * a) * zeta (Real.exp a * r))
    fun_prop
  have hCzero : Continuous (transportedEnergyCoefficient zeta 0) := by
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * 0) * zeta (Real.exp 0 * r))
    fun_prop
  have hia : IntervalIntegrable
      (transportedEnergyCoefficient zeta a) volume s R :=
    hCa.intervalIntegrable (μ := volume) (a := s) (b := R)
  have hi0 : IntervalIntegrable
      (transportedEnergyCoefficient zeta 0) volume s R :=
    hCzero.intervalIntegrable (μ := volume) (a := s) (b := R)
  have heq :
      transportedEnergyTail R zeta a s -
          transportedEnergyTail R zeta 0 s =
        ∫ r in s..R,
          (transportedEnergyCoefficient zeta a r -
            transportedEnergyCoefficient zeta 0 r) := by
    unfold transportedEnergyTail
    rw [intervalIntegral.integral_sub hia hi0]
  rw [heq]
  have hb :
      ∀ r ∈ Ι s R,
        ‖transportedEnergyCoefficient zeta a r -
            transportedEnergyCoefficient zeta 0 r‖ ≤ C * |a| := by
    intro r hr
    rw [uIoc_of_le hs.2] at hr
    exact transportedEnergyCoefficient_increment_bound
      R C zeta hzeta hC a ha r
      ⟨hs.1.le.trans hr.1.le, hr.2⟩
  have hint :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun r =>
        transportedEnergyCoefficient zeta a r -
          transportedEnergyCoefficient zeta 0 r) hb
  rw [abs_of_nonneg (sub_nonneg.mpr hs.2)] at hint
  calc
    ‖∫ r in s..R,
        (transportedEnergyCoefficient zeta a r -
          transportedEnergyCoefficient zeta 0 r)‖
        ≤ (C * |a|) * (R - s) := hint
    _ = |a| * (C * (R - s)) := by ring
    _ ≤ |a| * (C * R) := by
      gcongr
      nlinarith [hs.1.le]

/-- Strong L2 derivative at logarithmic scale zero for the corrected
energy-coordinate representer. -/
theorem transportedEnergyTailL2_hasDerivAt_zero
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    HasDerivAt
      (transportedEnergyTailL2 R hR zeta hzeta)
      (transportedEnergyTailScaleDerivativeL2 R hR zeta hzeta 0) 0 := by
  obtain ⟨C, hC0, hC⟩ :=
    transportedEnergyCoefficientDerivative_uniform_bound R zeta hzeta
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) R)
  let F : ℝ → ℝ → ℝ := fun a s => transportedEnergyTail R zeta a s
  let g : ℝ → ℝ := transportedEnergyTailScaleDerivative R zeta 0
  have hF (a : ℝ) : MemLp (F a) 2 μ := by
    dsimp [F, μ]
    exact continuous_memLp_restrict_Ioc 0 R hR
      (transportedEnergyTail R zeta a)
      (transportedEnergyTail_contDiff_one_in_s
        R zeta hzeta a).continuous 2
  have hg : MemLp g 2 μ := by
    dsimp [g, μ]
    exact continuous_memLp_restrict_Ioc 0 R hR
      (transportedEnergyTailScaleDerivative R zeta 0)
      (transportedEnergyTailScaleDerivative_contDiff_one
        R zeta hzeta 0).continuous 2
  have hw :
      Integrable (fun _ : ℝ => (C * R) ^ 2) μ := by
    dsimp [μ]
    exact (continuous_const :
      Continuous (fun _ : ℝ => (C * R) ^ 2)).integrableOn_Ioc
  have hI : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hb :
      ∀ᶠ a in 𝓝 (0 : ℝ),
        ∀ᵐ s ∂μ, ‖F a s - F 0 s‖ ≤ |a - 0| * (C * R) := by
    filter_upwards [hI] with a ha
    dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp [F]
    simpa using transportedEnergyTail_increment_bound
      R C hR hC0 zeta hzeta hC a ha s hs
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hgb :
      ∀ᵐ s ∂μ, ‖g s‖ ≤ C * R := by
    dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have ht := transportedEnergyTailScaleDerivative_abs_le
      R C zeta 0 s hs (fun r hr => hC 0 hzero r hr)
    dsimp [g]
    exact ht.trans (by
      gcongr
      nlinarith [hs.1.le])
  have hd :
      ∀ᵐ s ∂μ,
        HasDerivAt (fun a => F a s) (g s) 0 := by
    dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp [F, g]
    exact transportedEnergyTail_hasDerivAt_zero
      R s hR hs zeta hzeta
  have hstrong :=
    realLp2_hasDerivAt_of_increment_bound
      (μ := μ) F g 0 hF hg (fun _ => C * R) hw hb hgb hd
  change HasDerivAt
    (transportedEnergyTailL2 R hR zeta hzeta)
    (transportedEnergyTailScaleDerivativeL2
      R hR zeta hzeta 0) 0
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
