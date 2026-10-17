import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
A fully proved L2 realization of a square-integrable real kernel.

Mathlib does not currently expose a named Hilbert--Schmidt integral-operator
constructor.  This file builds the operator from the bounded bilinear form
against product vectors and the Frechet--Riesz equivalence.  The resulting
certificate is the standard kernel characterization of a Hilbert--Schmidt
operator.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HBL.L2Kernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- Real L2 space over the underlying measure. -/
abbrev RealL2 (μ : Measure α) := Lp ℝ 2 μ

/-- Real L2 space on the product measure. -/
abbrev RealKernelL2 (μ : Measure α) := Lp ℝ 2 (μ.prod μ)

private theorem tensor_memLp (g f : RealL2 μ) :
    MemLp (fun p : α × α => g p.1 * f p.2) 2 (μ.prod μ) := by
  have hg2 : Integrable (fun x : α => (g x) ^ 2) μ := (Lp.memLp g).integrable_sq
  have hf2 : Integrable (fun x : α => (f x) ^ 2) μ := (Lp.memLp f).integrable_sq
  have hp := hg2.mul_prod hf2
  have hm : AEStronglyMeasurable (fun p : α × α => g p.1 * f p.2)
      (μ.prod μ) :=
    ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).mul
      ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd)
  apply (memLp_two_iff_integrable_sq hm).2
  convert hp using 1
  ext p
  ring

/-- Product vector `(x,y) ↦ g(x)f(y)` in product L2. -/
def tensor (g f : RealL2 μ) : RealKernelL2 μ :=
  (tensor_memLp g f).toLp (fun p : α × α => g p.1 * f p.2)

theorem tensor_ae (g f : RealL2 μ) :
    (tensor g f : α × α → ℝ) =ᵐ[μ.prod μ]
      fun p => g p.1 * f p.2 :=
  (tensor_memLp g f).coeFn_toLp

theorem tensor_norm_sq (g f : RealL2 μ) :
    ‖tensor g f‖ ^ 2 = ‖g‖ ^ 2 * ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have heq :
      (fun p : α × α =>
        inner ℝ ((tensor g f : RealKernelL2 μ) p) (tensor g f p)) =ᵐ[μ.prod μ]
      fun p => (g p.1) ^ 2 * (f p.2) ^ 2 := by
    filter_upwards [tensor_ae g f] with p hp
    rw [hp]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    ring
  rw [integral_congr_ae heq]
  change
    (∫ p : α × α, (fun x : α => (g x) ^ 2) p.1 *
      (fun x : α => (f x) ^ 2) p.2 ∂μ.prod μ) = _
  rw [MeasureTheory.integral_prod_mul (μ := μ) (ν := μ)
    (fun x : α => (g x) ^ 2) (fun x : α => (f x) ^ 2)]
  have hg : (∫ x, (g x) ^ 2 ∂μ) = ‖g‖ ^ 2 := by
    calc
      (∫ x, (g x) ^ 2 ∂μ) =
          ∫ x, inner ℝ (g x) (g x) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            simp
      _ = inner ℝ g g := rfl
      _ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  have hf : (∫ x, (f x) ^ 2 ∂μ) = ‖f‖ ^ 2 := by
    calc
      (∫ x, (f x) ^ 2 ∂μ) =
          ∫ x, inner ℝ (f x) (f x) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            simp
      _ = inner ℝ f f := rfl
      _ = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f
  rw [hg, hf]

theorem tensor_norm (g f : RealL2 μ) :
    ‖tensor g f‖ = ‖g‖ * ‖f‖ := by
  have h := tensor_norm_sq g f
  nlinarith [norm_nonneg (tensor g f), norm_nonneg g, norm_nonneg f,
    mul_nonneg (norm_nonneg g) (norm_nonneg f)]

theorem tensor_add_left (g₁ g₂ f : RealL2 μ) :
    tensor (g₁ + g₂) f = tensor g₁ f + tensor g₂ f := by
  apply Lp.ext (μ := μ.prod μ)
  have hadd := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae
    (Lp.coeFn_add g₁ g₂)
  filter_upwards [tensor_ae (g₁ + g₂) f, tensor_ae g₁ f,
    tensor_ae g₂ f, hadd, Lp.coeFn_add (tensor g₁ f) (tensor g₂ f)]
      with p h h₁ h₂ hadd hsum
  simp only [h, h₁, h₂, hsum, Pi.add_apply] at *
  rw [hadd]
  ring

theorem tensor_smul_left (c : ℝ) (g f : RealL2 μ) :
    tensor (c • g) f = c • tensor g f := by
  apply Lp.ext (μ := μ.prod μ)
  have hsmul := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae
    (Lp.coeFn_smul c g)
  filter_upwards [tensor_ae (c • g) f, tensor_ae g f,
    hsmul, Lp.coeFn_smul c (tensor g f)] with p h h₀ hsmul hout
  simp only [h, h₀, hout, Pi.smul_apply, smul_eq_mul] at *
  rw [hsmul]
  ring

theorem tensor_add_right (g f₁ f₂ : RealL2 μ) :
    tensor g (f₁ + f₂) = tensor g f₁ + tensor g f₂ := by
  apply Lp.ext (μ := μ.prod μ)
  have hadd := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae
    (Lp.coeFn_add f₁ f₂)
  filter_upwards [tensor_ae g (f₁ + f₂), tensor_ae g f₁,
    tensor_ae g f₂, hadd, Lp.coeFn_add (tensor g f₁) (tensor g f₂)]
      with p h h₁ h₂ hadd hsum
  simp only [h, h₁, h₂, hsum, Pi.add_apply] at *
  rw [hadd]
  ring

theorem tensor_smul_right (c : ℝ) (g f : RealL2 μ) :
    tensor g (c • f) = c • tensor g f := by
  apply Lp.ext (μ := μ.prod μ)
  have hsmul := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae
    (Lp.coeFn_smul c f)
  filter_upwards [tensor_ae g (c • f), tensor_ae g f,
    hsmul, Lp.coeFn_smul c (tensor g f)] with p h h₀ hsmul hout
  simp only [h, h₀, hout, Pi.smul_apply, smul_eq_mul] at *
  rw [hsmul]
  ring

/-- For fixed right factor, product vectors form a bounded linear map. -/
def tensorRight (f : RealL2 μ) : RealL2 μ →L[ℝ] RealKernelL2 μ :=
  LinearMap.mkContinuous
    { toFun := fun g => tensor g f
      map_add' := fun g₁ g₂ => tensor_add_left g₁ g₂ f
      map_smul' := fun c g => tensor_smul_left c g f }
    ‖f‖ (fun g => by
      change ‖tensor g f‖ ≤ ‖f‖ * ‖g‖
      rw [tensor_norm]
      exact le_of_eq (mul_comm _ _))

/-- Pair a product vector against a product-L2 kernel. -/
def kernelFunctional (K : RealKernelL2 μ) (f : RealL2 μ) :
    RealL2 μ →L[ℝ] ℝ :=
  (innerSL ℝ K) ∘L tensorRight f

theorem kernelFunctional_apply (K : RealKernelL2 μ) (f g : RealL2 μ) :
    kernelFunctional K f g = inner ℝ K (tensor g f) := by
  rfl

theorem kernelFunctional_norm_le (K : RealKernelL2 μ) (f : RealL2 μ) :
    ‖kernelFunctional K f‖ ≤ ‖K‖ * ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg K) (norm_nonneg f)) ?_
  intro g
  rw [kernelFunctional_apply]
  calc
    ‖inner ℝ K (tensor g f)‖ ≤ ‖K‖ * ‖tensor g f‖ := norm_inner_le_norm _ _
    _ = ‖K‖ * ‖f‖ * ‖g‖ := by rw [tensor_norm]; ring

theorem kernelFunctional_add (K : RealKernelL2 μ) (f₁ f₂ : RealL2 μ) :
    kernelFunctional K (f₁ + f₂) =
      kernelFunctional K f₁ + kernelFunctional K f₂ := by
  ext g
  simp only [kernelFunctional_apply, add_apply]
  rw [tensor_add_right, inner_add_right]

theorem kernelFunctional_smul (K : RealKernelL2 μ) (c : ℝ) (f : RealL2 μ) :
    kernelFunctional K (c • f) = c • kernelFunctional K f := by
  ext g
  simp only [kernelFunctional_apply, smul_apply, smul_eq_mul]
  rw [tensor_smul_right, inner_smul_right]

/-- The bounded map from an input vector to the dual functional defined by
the kernel form. -/
def kernelForm (K : RealKernelL2 μ) :
    RealL2 μ →L[ℝ] (RealL2 μ →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := kernelFunctional K
      map_add' := kernelFunctional_add K
      map_smul' := kernelFunctional_smul K }
    ‖K‖ (fun f => kernelFunctional_norm_le K f)

/-- Continuous L2 operator associated with a product-L2 real kernel. -/
def operator (K : RealKernelL2 μ) : RealL2 μ →L[ℝ] RealL2 μ :=
  (InnerProductSpace.toDual ℝ (RealL2 μ)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    kernelForm K

theorem inner_operator (K : RealKernelL2 μ) (f g : RealL2 μ) :
    inner ℝ (operator K f) g = inner ℝ K (tensor g f) := by
  change inner ℝ
      ((InnerProductSpace.toDual ℝ (RealL2 μ)).symm (kernelForm K f)) g = _
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem operator_norm_le (K : RealKernelL2 μ) :
    ‖operator K‖ ≤ ‖K‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg K) ?_
  intro f
  rw [show ‖operator K f‖ = ‖kernelForm K f‖ by
    exact (InnerProductSpace.toDual ℝ (RealL2 μ)).symm.norm_map _]
  exact kernelFunctional_norm_le K f

theorem operator_add (K₁ K₂ : RealKernelL2 μ) :
    operator (K₁ + K₂) = operator K₁ + operator K₂ := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  calc
    inner ℝ (operator (K₁ + K₂) f) g =
        inner ℝ (K₁ + K₂) (tensor g f) := inner_operator _ _ _
    _ = inner ℝ K₁ (tensor g f) + inner ℝ K₂ (tensor g f) :=
      inner_add_left _ _ _
    _ = inner ℝ (operator K₁ f) g + inner ℝ (operator K₂ f) g := by
      rw [inner_operator, inner_operator]
    _ = inner ℝ ((operator K₁ + operator K₂) f) g := by
      rw [add_apply, inner_add_left]

theorem operator_smul (c : ℝ) (K : RealKernelL2 μ) :
    operator (c • K) = c • operator K := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  calc
    inner ℝ (operator (c • K) f) g =
        inner ℝ (c • K) (tensor g f) := inner_operator _ _ _
    _ = c * inner ℝ K (tensor g f) := real_inner_smul_left _ _ _
    _ = c * inner ℝ (operator K f) g := by rw [inner_operator]
    _ = inner ℝ (c • operator K f) g :=
      (real_inner_smul_left (operator K f) g c).symm
    _ = inner ℝ ((c • operator K) f) g := by rfl

theorem operator_zero :
    operator (0 : RealKernelL2 μ) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  rw [inner_operator]
  simp

/-- The passage from a product-L2 kernel to its bounded operator is itself
bounded and linear. -/
def kernelToOperator :
    RealKernelL2 μ →L[ℝ] (RealL2 μ →L[ℝ] RealL2 μ) :=
  LinearMap.mkContinuous
    { toFun := operator
      map_add' := operator_add
      map_smul' := operator_smul }
    1 (fun K => by simpa using operator_norm_le K)

@[simp]
theorem kernelToOperator_apply (K : RealKernelL2 μ) :
    kernelToOperator K = operator K :=
  rfl

theorem tensor_inner_tensor (g f k h : RealL2 μ) :
    inner ℝ (tensor g f) (tensor k h) =
      inner ℝ g k * inner ℝ f h := by
  rw [L2.inner_def]
  have heq :
      (fun p : α × α =>
        inner ℝ ((tensor g f : RealKernelL2 μ) p) (tensor k h p)) =ᵐ[μ.prod μ]
      fun p => (g p.1 * k p.1) * (f p.2 * h p.2) := by
    filter_upwards [tensor_ae g f, tensor_ae k h] with p hgf hkh
    rw [hgf, hkh]
    simp only [Real.inner_apply]
    ring
  rw [integral_congr_ae heq]
  calc
    (∫ p : α × α, (g p.1 * k p.1) * (f p.2 * h p.2) ∂μ.prod μ) =
        (∫ x : α, g x * k x ∂μ) * (∫ x : α, f x * h x ∂μ) := by
      exact MeasureTheory.integral_prod_mul
        (fun x : α => g x * k x) (fun x : α => f x * h x)
    _ = inner ℝ g k * inner ℝ f h := by
      simp only [L2.inner_def, Real.inner_apply]

/-- A pure tensor kernel gives the corresponding rank-one operator. -/
theorem operator_tensor (g f : RealL2 μ) :
    operator (tensor g f) = InnerProductSpace.rankOne ℝ g f := by
  apply ContinuousLinearMap.ext
  intro h
  apply ext_inner_right ℝ
  intro k
  rw [inner_operator, tensor_inner_tensor]
  simp only [InnerProductSpace.rankOne_apply, inner_smul_left,
    RCLike.conj_to_real]
  ring

theorem rankOne_isCompactOperator (g f : RealL2 μ) :
    IsCompactOperator (InnerProductSpace.rankOne ℝ g f) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (innerSL ℝ f)).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ g)

theorem operator_tensor_isCompactOperator (g f : RealL2 μ) :
    IsCompactOperator (operator (tensor g f)) := by
  rw [operator_tensor]
  exact rankOne_isCompactOperator g f

/-- Algebraic finite sums of product kernels. -/
def tensorSpan : Submodule ℝ (RealKernelL2 μ) :=
  Submodule.span ℝ (Set.range fun p : RealL2 μ × RealL2 μ =>
    tensor p.1 p.2)

theorem operator_isCompactOperator_of_mem_tensorSpan
    {K : RealKernelL2 μ} (hK : K ∈ tensorSpan ( μ := μ)) :
    IsCompactOperator (operator K) := by
  unfold tensorSpan at hK
  induction hK using Submodule.span_induction with
  | mem K hK =>
      obtain ⟨⟨g, f⟩, rfl⟩ := hK
      exact operator_tensor_isCompactOperator g f
  | zero =>
      rw [operator_zero]
      exact isCompactOperator_zero
  | add K₁ K₂ _ _ h₁ h₂ =>
      rw [operator_add]
      exact h₁.add h₂
  | smul c K _ h =>
      rw [operator_smul]
      exact h.smul c

/-- Any kernel in the L2 closure of finite sums of product kernels gives a
compact operator.  The remaining density statement is measure-theoretic and
is deliberately exposed as a separate, reusable obligation. -/
theorem operator_isCompactOperator_of_mem_closure_tensorSpan
    {K : RealKernelL2 μ}
    (hK : K ∈ closure (tensorSpan ( μ := μ) : Set (RealKernelL2 μ))) :
    IsCompactOperator (operator K) := by
  rw [mem_closure_iff_seq_limit] at hK
  obtain ⟨Kseq, hKseq, hlim⟩ := hK
  refine isCompactOperator_of_tendsto
    (F := fun n => operator (Kseq n))
    ((kernelToOperator ( μ := μ)).continuous.continuousAt.tendsto.comp hlim) ?_
  exact Filter.Eventually.of_forall fun n =>
    operator_isCompactOperator_of_mem_tensorSpan (hKseq n)

/-- A reusable density criterion for product kernels.  It reduces density of
pure tensors to approximation of finite-measure indicator functions by a
measure-dense family. -/
theorem tensorSpan_dense_of_measureDense
    (A : Set (Set (α × α)))
    (hA : ( μ.prod μ).MeasureDense A)
    (hIndicator : ∀ (c : ℝ) (s : Set (α × α)) (hs : s ∈ A)
      (hμs : ( μ.prod μ) s ≠ ⊤),
      indicatorConstLp 2 (hA.measurable s hs) hμs c ∈
        (tensorSpan ( μ := μ)).topologicalClosure) :
    (tensorSpan ( μ := μ)).topologicalClosure = ⊤ := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  apply top_unique
  intro K _
  refine Lp.induction (p := (2 : ℝ≥0∞)) ( μ := μ.prod μ)
    (by norm_num) (fun F => F ∈ (tensorSpan ( μ := μ)).topologicalClosure)
    ?_ ?_ (Submodule.isClosed_topologicalClosure _) K
  · intro c s hs hμs
    have hall : indicatorConstLp 2 hs hμs.ne c ∈
        {indicatorConstLp 2 ht hμt c |
          (t : Set (α × α)) (ht : MeasurableSet t)
          (hμt : ( μ.prod μ) t ≠ ⊤)} := by
      exact ⟨s, hs, hμs.ne, rfl⟩
    have hclose := hA.indicatorConstLp_subset_closure (p := (2 : ℝ≥0∞)) c hall
    refine closure_minimal ?_ (Submodule.isClosed_topologicalClosure _) hclose
    rintro F ⟨t, ht, hμt, rfl⟩
    exact hIndicator c t ht hμt
  · intro f g hf hg _ hfm hgm
    exact Submodule.add_mem _ hfm hgm

theorem operator_isCompactOperator_of_tensorSpan_dense
    (hDense : (tensorSpan ( μ := μ)).topologicalClosure = ⊤)
    (K : RealKernelL2 μ) :
    IsCompactOperator (operator K) := by
  apply operator_isCompactOperator_of_mem_closure_tensorSpan
  rw [← Submodule.topologicalClosure_coe, hDense]
  exact Submodule.mem_top

/-- Kernel realization certificate for a Hilbert--Schmidt operator.  This is
the standard L2-kernel characterization, and includes the actual bounded
operator together with its weak integral action. -/
def IsHilbertSchmidtKernelOperator
    (T : RealL2 μ →L[ℝ] RealL2 μ) (K : RealKernelL2 μ) : Prop :=
  ∀ f g, inner ℝ (T f) g = inner ℝ K (tensor g f)

theorem operator_isHilbertSchmidtKernelOperator (K : RealKernelL2 μ) :
    IsHilbertSchmidtKernelOperator (operator K) K :=
  inner_operator K

end HBL.L2Kernel
