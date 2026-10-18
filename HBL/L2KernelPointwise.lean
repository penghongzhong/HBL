import HBL.L2KernelCompact
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
Almost-everywhere pointwise action of the real Hilbert--Schmidt kernel
operator constructed in `HBL.L2KernelOperator`.

The proof does not presuppose that the pointwise integral is globally L1.
It identifies it locally on every measurable finite-measure set, using the
corresponding L2 indicator as a test vector and Fubini's theorem.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HBL.L2Kernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]

/-- The abstract L2 kernel operator agrees almost everywhere with integration
against any concrete representative used to construct its kernel. -/
theorem operator_toLp_ae_eq_integral
    (k : α → α → ℝ)
    (hk : MemLp (Function.uncurry k) 2 (μ.prod μ))
    (f : RealL2 μ) :
    (operator (hk.toLp (Function.uncurry k)) f : α → ℝ) =ᵐ[μ]
      fun x => ∫ y, k x y * f y ∂μ := by
  let K : RealKernelL2 μ := hk.toLp (Function.uncurry k)
  let out : RealL2 μ := operator K f
  let h : α → ℝ := fun x => ∫ y, k x y * f y ∂μ
  have hKae : (K : α × α → ℝ) =ᵐ[μ.prod μ]
      Function.uncurry k := hk.coeFn_toLp
  have houtLocal : ∀ s : Set α, MeasurableSet s → μ s < ∞ →
      IntegrableOn (out : α → ℝ) s μ := by
    intro s hs hμs
    rw [IntegrableOn]
    letI : IsFiniteMeasure (μ.restrict s) :=
      isFiniteMeasure_restrict.2 hμs.ne
    exact ((Lp.memLp out).mono_measure Measure.restrict_le_self).integrable
      (by norm_num)
  have hhLocal : ∀ s : Set α, MeasurableSet s → μ s < ∞ →
      IntegrableOn h s μ := by
    intro s hs hμs
    let g : RealL2 μ := indicatorConstLp 2 hs hμs.ne (1 : ℝ)
    have hprod : Integrable (fun p : α × α =>
        k p.1 p.2 * (g p.1 * f p.2)) (μ.prod μ) := by
      have hbase := hk.integrable_mul (Lp.memLp (tensor g f))
      refine hbase.congr ?_
      filter_upwards [tensor_ae g f] with p ht
      change k p.1 p.2 * (tensor g f : α × α → ℝ) p =
        k p.1 p.2 * (g p.1 * f p.2)
      rw [ht]
    have hiter : Integrable (fun x : α => ∫ y : α,
        k x y * (g x * f y) ∂μ) μ := hprod.integral_prod_left
    have heq : (fun x : α => ∫ y : α,
        k x y * (g x * f y) ∂μ) =ᵐ[μ]
          s.indicator h := by
      filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ))] with x hx
      calc
        (∫ y : α, k x y * (g x * f y) ∂μ) =
            g x * ∫ y : α, k x y * f y ∂μ := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with y
          ring
        _ = s.indicator h x := by
          rw [hx]
          by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs, h]
    have hindicator : Integrable (s.indicator h) μ := hiter.congr heq
    exact (integrable_indicator_iff hs).mp hindicator
  have hsetIntegral : ∀ s : Set α, MeasurableSet s → μ s < ∞ →
      (∫ x in s, (out : α → ℝ) x ∂μ) = ∫ x in s, h x ∂μ := by
    intro s hs hμs
    let g : RealL2 μ := indicatorConstLp 2 hs hμs.ne (1 : ℝ)
    have hprod : Integrable (fun p : α × α =>
        k p.1 p.2 * (g p.1 * f p.2)) (μ.prod μ) := by
      have hbase := hk.integrable_mul (Lp.memLp (tensor g f))
      refine hbase.congr ?_
      filter_upwards [tensor_ae g f] with p ht
      change k p.1 p.2 * (tensor g f : α × α → ℝ) p =
        k p.1 p.2 * (g p.1 * f p.2)
      rw [ht]
    have heq : (fun x : α => ∫ y : α,
        k x y * (g x * f y) ∂μ) =ᵐ[μ]
          s.indicator h := by
      filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ))] with x hx
      calc
        (∫ y : α, k x y * (g x * f y) ∂μ) =
            g x * ∫ y : α, k x y * f y ∂μ := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with y
          ring
        _ = s.indicator h x := by
          rw [hx]
          by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs, h]
    calc
      (∫ x in s, (out : α → ℝ) x ∂μ) = inner ℝ g out := by
        exact (L2.inner_indicatorConstLp_one hs hμs.ne out).symm
      _ = inner ℝ out g := real_inner_comm _ _
      _ = inner ℝ K (tensor g f) := inner_operator K f g
      _ = ∫ p : α × α,
          k p.1 p.2 * (g p.1 * f p.2) ∂(μ.prod μ) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hKae, tensor_ae g f] with p hkp ht
        rw [hkp, ht, Real.inner_apply]
        rfl
      _ = ∫ x : α, ∫ y : α,
          k x y * (g x * f y) ∂μ ∂μ := integral_prod _ hprod
      _ = ∫ x in s, h x ∂μ := by
        rw [← integral_indicator hs]
        exact integral_congr_ae heq
  change (out : α → ℝ) =ᵐ[μ] h
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    houtLocal hhLocal hsetIntegral

end HBL.L2Kernel
