import HBL.TransportedEnergyLocalDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
C1 regularity of the corrected transported energy dual.

The previous module proves strong L2 differentiability at every scale in
(-1,1). Here the derivative vector is proved continuous in L2, hence the
correct transported representer is C1 at zero. Applying the real Riesz
isometry then gives C1 regularity in operator norm for the actual threshold
functional used by the modulation implicit-function theorem.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval RealInnerProductSpace

namespace HBL.Modulation

theorem transportedEnergyTailScaleDerivative_continuousAt_in_a
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a₀ : ℝ) (ha₀ : a₀ ∈ Ioo (-1 : ℝ) 1)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) :
    ContinuousAt
      (fun a : ℝ => transportedEnergyTailScaleDerivative R zeta a s) a₀ := by
  obtain ⟨C, hC0, hC⟩ :=
    transportedEnergyCoefficientDerivative_uniform_bound R zeta hzeta
  have hI : Icc (-1 : ℝ) 1 ∈ 𝓝 a₀ :=
    Icc_mem_nhds ha₀.1 ha₀.2
  have hFmeas :
      ∀ᶠ a in 𝓝 a₀,
        AEStronglyMeasurable
          (transportedEnergyCoefficientDerivative zeta a)
          ((volume : Measure ℝ).restrict (Ι s R)) := by
    apply Filter.Eventually.of_forall
    intro a
    have hz : Continuous zeta := hzeta.continuous
    have hdz : Continuous (deriv zeta) := hzeta.continuous_deriv_one
    have hc : Continuous
        (transportedEnergyCoefficientDerivative zeta a) := by
      change Continuous (fun r : ℝ =>
        Real.exp ((3 / 2 : ℝ) * a) *
          ((3 / 2 : ℝ) * zeta (Real.exp a * r) +
            (Real.exp a * r) * deriv zeta (Real.exp a * r)))
      fun_prop
    exact hc.aestronglyMeasurable
  have hbound :
      ∀ᶠ a in 𝓝 a₀,
        ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ι s R →
          ‖transportedEnergyCoefficientDerivative zeta a r‖ ≤ C := by
    filter_upwards [hI] with a ha
    apply Filter.Eventually.of_forall
    intro r hr
    rw [uIoc_of_le hs.2] at hr
    exact hC a ha r ⟨hs.1.le.trans hr.1.le, hr.2⟩
  have hCint :
      IntervalIntegrable (fun _ : ℝ => C) volume s R :=
    continuous_const.intervalIntegrable (μ := volume) (a := s) (b := R)
  have hcont :
      ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ι s R →
        ContinuousAt
          (fun a : ℝ =>
            transportedEnergyCoefficientDerivative zeta a r) a₀ := by
    apply Filter.Eventually.of_forall
    intro r _
    have hz : Continuous zeta := hzeta.continuous
    have hdz : Continuous (deriv zeta) := hzeta.continuous_deriv_one
    change ContinuousAt
      (fun a : ℝ =>
        Real.exp ((3 / 2 : ℝ) * a) *
          ((3 / 2 : ℝ) * zeta (Real.exp a * r) +
            (Real.exp a * r) * deriv zeta (Real.exp a * r))) a₀
    fun_prop
  change ContinuousAt
    (fun a : ℝ =>
      ∫ r in s..R, transportedEnergyCoefficientDerivative zeta a r) a₀
  exact intervalIntegral.continuousAt_of_dominated_interval
    (μ := volume)
    (F := fun a r => transportedEnergyCoefficientDerivative zeta a r)
    (x₀ := a₀) (bound := fun _ => C)
    hFmeas hbound hCint hcont

theorem transportedEnergyTailScaleDerivativeL2_continuousAt_of_mem
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a₀ : ℝ) (ha₀ : a₀ ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt
      (transportedEnergyTailScaleDerivativeL2 R hR zeta hzeta) a₀ := by
  obtain ⟨C, hC0, hC⟩ :=
    transportedEnergyCoefficientDerivative_uniform_bound R zeta hzeta
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) R)
  let F : ℝ → ℝ → ℝ :=
    fun a s => transportedEnergyTailScaleDerivative R zeta a s
  let g : ℝ → ℝ :=
    transportedEnergyTailScaleDerivative R zeta a₀
  have hF (a : ℝ) : MemLp (F a) 2 μ := by
    dsimp [F, μ]
    exact continuous_memLp_restrict_Ioc 0 R hR
      (transportedEnergyTailScaleDerivative R zeta a)
      (transportedEnergyTailScaleDerivative_contDiff_one
        R zeta hzeta a).continuous 2
  have hg : MemLp g 2 μ := by
    dsimp [g, μ]
    exact continuous_memLp_restrict_Ioc 0 R hR
      (transportedEnergyTailScaleDerivative R zeta a₀)
      (transportedEnergyTailScaleDerivative_contDiff_one
        R zeta hzeta a₀).continuous 2
  have hw :
      Integrable (fun _ : ℝ => (2 * (C * R)) ^ 2) μ := by
    dsimp [μ]
    exact (continuous_const :
      Continuous (fun _ : ℝ => (2 * (C * R)) ^ 2)).integrableOn_Ioc
  have hI : Icc (-1 : ℝ) 1 ∈ 𝓝 a₀ :=
    Icc_mem_nhds ha₀.1 ha₀.2
  have ha₀cc : a₀ ∈ Icc (-1 : ℝ) 1 :=
    ⟨ha₀.1.le, ha₀.2.le⟩
  have hb :
      ∀ᶠ a in 𝓝 a₀,
        ∀ᵐ s ∂μ, ‖F a s - g s‖ ≤ 2 * (C * R) := by
    filter_upwards [hI] with a ha
    dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hFa :=
      transportedEnergyTailScaleDerivative_abs_le
        R C zeta a s hs (fun r hr => hC a ha r hr)
    have hFg :=
      transportedEnergyTailScaleDerivative_abs_le
        R C zeta a₀ s hs (fun r hr => hC a₀ ha₀cc r hr)
    have hshort : C * (R - s) ≤ C * R := by
      gcongr
      linarith [hs.1.le]
    have hFa' : ‖F a s‖ ≤ C * R := by
      dsimp [F]
      exact hFa.trans hshort
    have hFg' : ‖g s‖ ≤ C * R := by
      dsimp [g]
      exact hFg.trans hshort
    exact (norm_sub_le _ _).trans (by
      calc
        ‖F a s‖ + ‖g s‖ ≤ C * R + C * R :=
          add_le_add hFa' hFg'
        _ = 2 * (C * R) := by ring)
  have hlim :
      ∀ᵐ s ∂μ,
        Tendsto (fun a => F a s) (𝓝 a₀) (𝓝 (g s)) := by
    dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp [F, g]
    exact transportedEnergyTailScaleDerivative_continuousAt_in_a
      R hR zeta hzeta a₀ ha₀ s hs
  have ht :=
    realLp2_tendsto_dominated F g hF hg
      (fun _ => 2 * (C * R)) hw hb hlim
  have hsource :
      (fun a => (hF a).toLp (F a)) =
        transportedEnergyTailScaleDerivativeL2 R hR zeta hzeta := by
    funext a
    dsimp [F, μ]
    unfold transportedEnergyTailScaleDerivativeL2
    apply MemLp.toLp_congr
    exact Filter.EventuallyEq.rfl
  have htarget :
      hg.toLp g =
        transportedEnergyTailScaleDerivativeL2 R hR zeta hzeta a₀ := by
    dsimp [g, μ]
    unfold transportedEnergyTailScaleDerivativeL2
    apply MemLp.toLp_congr
    exact Filter.EventuallyEq.rfl
  rw [hsource, htarget] at ht
  exact ht

theorem transportedEnergyTailScaleDerivativeL2_continuousOn
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    ContinuousOn
      (transportedEnergyTailScaleDerivativeL2 R hR zeta hzeta)
      (Ioo (-1 : ℝ) 1) := by
  intro a ha
  exact (transportedEnergyTailScaleDerivativeL2_continuousAt_of_mem
    R hR zeta hzeta a ha).continuousWithinAt

theorem transportedEnergyTailL2_contDiffAt_zero
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    ContDiffAt ℝ 1
      (transportedEnergyTailL2 R hR zeta hzeta) 0 := by
  rw [contDiffAt_one_iff]
  let V := RadialEnergyL2 R
  let D : ℝ → V :=
    transportedEnergyTailScaleDerivativeL2 R hR zeta hzeta
  let Dlin : ℝ → (ℝ →L[ℝ] V) :=
    fun a => ContinuousLinearMap.toSpanSingleton ℝ (D a)
  refine ⟨Dlin, Ioo (-1 : ℝ) 1,
    Ioo_mem_nhds (by norm_num) (by norm_num), ?_, ?_⟩
  · have hD :
        ContinuousOn D (Ioo (-1 : ℝ) 1) := by
      simpa [D, V] using
        transportedEnergyTailScaleDerivativeL2_continuousOn
          R hR zeta hzeta
    have hspan :
        Continuous
          (ContinuousLinearMap.toSpanSingleton ℝ :
            V → (ℝ →L[ℝ] V)) :=
      (ContinuousLinearMap.toSpanSingletonCLE
        (𝕜 := ℝ) (E := V)).continuous
    exact hspan.comp_continuousOn hD
  · intro a ha
    have hd :=
      transportedEnergyTailL2_hasDerivAt_of_mem
        R hR zeta hzeta a ha
    change HasFDerivAt
      (transportedEnergyTailL2 R hR zeta hzeta)
      (Dlin a) a
    simpa [Dlin, D, V] using hd.hasFDerivAt

theorem transportedEnergyThresholdDual_contDiffAt_zero
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    ContDiffAt ℝ 1
      (transportedEnergyThresholdDual R hR zeta hzeta) 0 := by
  let V := RadialEnergyL2 R
  let L : V →L[ℝ] (V →L[ℝ] ℝ) :=
    (InnerProductSpace.toDualMap ℝ V).toContinuousLinearMap
  have hQ :=
    transportedEnergyTailL2_contDiffAt_zero R hR zeta hzeta
  have hcomp :=
    L.contDiff.contDiffAt.comp 0 hQ
  change ContDiffAt ℝ 1
    (fun a : ℝ => innerSL ℝ
      (transportedEnergyTailL2 R hR zeta hzeta a)) 0
  simpa [L, V, Function.comp_def] using hcomp

end HBL.Modulation
