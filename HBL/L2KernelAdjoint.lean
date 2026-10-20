import HBL.L2KernelOperator

/-!
The adjoint of an actual square-integrable real kernel operator is the
operator of its transposed kernel.  The proof uses the existing kernel
bilinear form and the measure-preserving swap on the product space.
-/

noncomputable section

open MeasureTheory

namespace HBL.L2Kernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- Transposing a square-integrable real kernel preserves its `MemLp`
property on the same product measure. -/
theorem kernel_transpose_memLp (k : α → α → ℝ)
    (hk : MemLp (Function.uncurry k) 2 (μ.prod μ)) :
    MemLp (Function.uncurry (fun x y => k y x)) 2 (μ.prod μ) := by
  exact hk.comp_measurePreserving Measure.measurePreserving_swap

private theorem inner_toLp_tensor_integral (k : α → α → ℝ)
    (hk : MemLp (Function.uncurry k) 2 (μ.prod μ)) (f g : RealL2 μ) :
    inner ℝ (hk.toLp (Function.uncurry k)) (tensor g f) =
      ∫ p : α × α, k p.1 p.2 * (g p.1 * f p.2) ∂μ.prod μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hk.coeFn_toLp, tensor_ae g f] with p hK ht
  rw [hK, ht, Real.inner_apply]
  rfl

/-- The Hilbert adjoint of the actual `L²` kernel operator is exactly the
operator built from the transposed kernel.  All integrability and adjoint
identities are proved from the sole square-integrability input. -/
theorem operator_toLp_adjoint_eq_transpose (k : α → α → ℝ)
    (hk : MemLp (Function.uncurry k) 2 (μ.prod μ)) :
    ContinuousLinearMap.adjoint (operator (hk.toLp (Function.uncurry k))) =
      operator ((kernel_transpose_memLp k hk).toLp
        (Function.uncurry (fun x y => k y x))) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [inner_operator, ← real_inner_comm f, inner_operator,
    inner_toLp_tensor_integral, inner_toLp_tensor_integral]
  calc
    (∫ p : α × α, k p.2 p.1 * (g p.1 * f p.2) ∂μ.prod μ) =
        ∫ p : α × α,
          (fun q : α × α => k q.1 q.2 * (f q.1 * g q.2)) p.swap ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards with p
      change k p.2 p.1 * (g p.1 * f p.2) = k p.2 p.1 * (f p.2 * g p.1)
      ring
    _ = ∫ p : α × α, k p.1 p.2 * (f p.1 * g p.2) ∂μ.prod μ :=
      MeasureTheory.integral_prod_swap
        (μ := μ) (ν := μ) (fun q : α × α => k q.1 q.2 * (f q.1 * g q.2))

end HBL.L2Kernel
