import HBL.L2DominatedDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-!
Strong L2 differentiation of the actual transported compact radial test.

The transported kernel has a uniformly bounded scale derivative on
[-1,1] × [0,R].  The one-dimensional mean-value theorem therefore gives
a uniform Lipschitz increment estimate for the kernel and hence for its
tail primitive Q_a(s).  The dominated L2 differentiation theorem from
HBL.L2DominatedDerivative then upgrades the already verified pointwise
derivative to a derivative in the radial-energy Hilbert norm.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace HBL.Modulation

/-- Mean-value estimate for the actual transported radial test kernel. -/
theorem transportedRadialTest_increment_bound
    (R C : ℝ) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hC : ∀ a ∈ Icc (-1 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) R,
      ‖transportedRadialTestDerivative zeta a r‖ ≤ C)
    (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
    ‖transportedRadialTest zeta a r -
        transportedRadialTest zeta 0 r‖ ≤ C * |a| := by
  have hder :
      ∀ b ∈ Icc (-1 : ℝ) 1,
        HasDerivWithinAt
          (fun x : ℝ => transportedRadialTest zeta x r)
          (transportedRadialTestDerivative zeta b r)
          (Icc (-1 : ℝ) 1) b := by
    intro b hb
    exact (transportedRadialTest_hasDerivAt zeta hzeta b r).hasDerivWithinAt
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hmv :=
    (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      hder (fun b hb => hC b hb r hr) h0 ha
  simpa [Real.norm_eq_abs] using hmv

/-- Uniform increment estimate for the tail representer on the physical
radial interval. -/
theorem transportedTestTail_increment_bound
    (R C : ℝ) (hR : 0 ≤ R) (hC0 : 0 ≤ C)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hC : ∀ a ∈ Icc (-1 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) R,
      ‖transportedRadialTestDerivative zeta a r‖ ≤ C)
    (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) :
    ‖transportedTestTail R zeta a s -
        transportedTestTail R zeta 0 s‖ ≤ |a| * (C * R) := by
  have hz : Continuous zeta := hzeta.continuous
  have hKa : Continuous (transportedRadialTest zeta a) := by
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * a) * zeta (Real.exp a * r) * r)
    fun_prop
  have hK0 : Continuous (transportedRadialTest zeta 0) := by
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * 0) * zeta (Real.exp 0 * r) * r)
    fun_prop
  have hia : IntervalIntegrable (transportedRadialTest zeta a) volume s R :=
    hKa.intervalIntegrable (μ := volume) (a := s) (b := R)
  have hi0 : IntervalIntegrable (transportedRadialTest zeta 0) volume s R :=
    hK0.intervalIntegrable (μ := volume) (a := s) (b := R)
  have heq :
      transportedTestTail R zeta a s - transportedTestTail R zeta 0 s =
        ∫ r in s..R,
          (transportedRadialTest zeta a r -
            transportedRadialTest zeta 0 r) := by
    unfold transportedTestTail
    rw [intervalIntegral.integral_sub hia hi0]
  rw [heq]
  have hsR : s ≤ R := hs.2
  have hb :
      ∀ r ∈ Ι s R,
        ‖transportedRadialTest zeta a r -
            transportedRadialTest zeta 0 r‖ ≤ C * |a| := by
    intro r hr
    rw [uIoc_of_le hsR] at hr
    exact transportedRadialTest_increment_bound R C zeta hzeta hC a ha r
      ⟨hs.1.le.trans hr.1.le, hr.2⟩
  have hint :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun r =>
        transportedRadialTest zeta a r - transportedRadialTest zeta 0 r)
      hb
  rw [abs_of_nonneg (sub_nonneg.mpr hsR)] at hint
  calc
    ‖∫ r in s..R,
        (transportedRadialTest zeta a r -
          transportedRadialTest zeta 0 r)‖
        ≤ (C * |a|) * (R - s) := hint
    _ = |a| * (C * (R - s)) := by ring
    _ ≤ |a| * (C * R) := by
      gcongr
      nlinarith [hs.1.le]

/-- The actual transported test representer is differentiable at scale zero
in the radial-energy L2 norm, with derivative given by the bundled
scale-derivative tail. -/
theorem transportedTestTailL2_hasDerivAt_zero
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    HasDerivAt
      (transportedTestTailL2 R hR zeta hzeta)
      (transportedTestTailScaleDerivativeL2 R hR zeta hzeta 0) 0 := by
  obtain ⟨C, hC0, hC⟩ :=
    transportedRadialTestDerivative_uniform_bound 1 R zeta hzeta
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) R)
  let F : ℝ → ℝ → ℝ := fun a s => transportedTestTail R zeta a s
  let g : ℝ → ℝ := transportedTestTailScaleDerivative R zeta 0
  have hF (a : ℝ) : MemLp (F a) 2 μ := by
    dsimp [F, μ]
    exact continuous_memLp_restrict_Ioc 0 R hR
      (transportedTestTail R zeta a)
      (transportedTestTail_contDiff_one_in_s R zeta hzeta a).continuous 2
  have hg : MemLp g 2 μ := by
    dsimp [g, μ]
    exact continuous_memLp_restrict_Ioc 0 R hR
      (transportedTestTailScaleDerivative R zeta 0)
      (transportedTestTailScaleDerivative_contDiff_one
        R zeta hzeta 0).continuous 2
  have hw :
      Integrable (fun _ : ℝ => (C * R) ^ 2) μ := by
    dsimp [μ]
    exact (continuous_const : Continuous (fun _ : ℝ => (C * R) ^ 2)).integrableOn_Ioc
  have hI : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hb :
      ∀ᶠ a in 𝓝 (0 : ℝ),
        ∀ᵐ s ∂μ, ‖F a s - F 0 s‖ ≤ |a - 0| * (C * R) := by
    filter_upwards [hI] with a ha
    dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp [F]
    simpa using
      transportedTestTail_increment_bound
        R C hR hC0 zeta hzeta hC a ha s hs
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hgb :
      ∀ᵐ s ∂μ, ‖g s‖ ≤ C * R := by
    dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have ht :=
      transportedTestTailScaleDerivative_abs_le
        R C zeta 0 s hs.1.le hs.2
        (fun r hr => hC 0 hzero r hr)
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
    exact transportedTestTail_hasDerivAt_zero_as_scaleDerivative
      R s hR hs.1.le zeta hzeta
  have hstrong :=
    realLp2_hasDerivAt_of_increment_bound
      (μ := μ) F g 0 hF hg (fun _ => C * R) hw hb hgb hd
  simpa [F, g, μ, transportedTestTailL2,
    transportedTestTailScaleDerivativeL2] using hstrong

end HBL.Modulation
