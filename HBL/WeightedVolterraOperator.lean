import HBL.WeightedVolterraKernel
import HBL.L2KernelAdjoint
import HBL.L2KernelComposition

/-!
The actual weighted Volterra operator and its Green factorization.

The concrete kernel is `a(r) 1_{0<s<r}`, with `a(r) = (1+r²)⁻¹`.
Its proved product-L2 realization defines the bounded operator below.
The transpose-kernel adjoint theorem and the proved overlap integral give
`V V* = G` for the existing weighted free Green operator.  The primitive
and tail formulas identify the actual almost-everywhere representatives;
no global L1 assumption is imposed on an arbitrary L2 input.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The actual bounded Volterra map on half-line L2. -/
def weightedVolterraOperator :
    RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure :=
  operator (weightedVolterraKernel_memLp.toLp
    (Function.uncurry weightedVolterraKernel))

/-- The actual Volterra operator is compact because its kernel is L2. -/
theorem weightedVolterraOperator_compact :
    IsCompactOperator weightedVolterraOperator :=
  operator_isCompactOperator _

/-- The Hilbert adjoint is the operator of the actual transposed kernel. -/
theorem weightedVolterraOperator_adjoint :
    ContinuousLinearMap.adjoint weightedVolterraOperator =
      operator ((kernel_transpose_memLp weightedVolterraKernel
        weightedVolterraKernel_memLp).toLp
          (Function.uncurry (fun r s => weightedVolterraKernel s r))) :=
  operator_toLp_adjoint_eq_transpose weightedVolterraKernel
    weightedVolterraKernel_memLp

/-- The actual weighted free Green operator is `V V*`.
The kernel composition uses the proved interval-overlap identity. -/
theorem weightedVolterraOperator_comp_adjoint :
    weightedVolterraOperator ∘L
        ContinuousLinearMap.adjoint weightedVolterraOperator =
      weightedFreeGreenOperator := by
  rw [weightedVolterraOperator_adjoint]
  exact operator_comp_toLp_eq_of_convolution
    (μ := halfLineMeasure) (fun r : ℝ => 0 < r)
    (ae_restrict_mem measurableSet_Ioi)
    weightedVolterraKernel (fun r s => weightedVolterraKernel s r)
    weightedFreeGreen weightedVolterraKernel_memLp
    (kernel_transpose_memLp weightedVolterraKernel weightedVolterraKernel_memLp)
    weightedFreeGreen_memLp_two
    (fun r s _ _ => weightedVolterraKernel_nonneg r s)
    (fun r s _ _ => weightedVolterraKernel_nonneg s r)
    (fun r rho hr hrho => weightedVolterraKernel_overlap r rho hr hrho)

/-- Every L2 input has the actual weighted-primitive representative. -/
theorem weightedVolterraOperator_ae_pointwise
    (f : RealL2 halfLineMeasure) :
    (weightedVolterraOperator f : ℝ → ℝ) =ᵐ[halfLineMeasure]
      fun r => (1 + r ^ 2)⁻¹ * ∫ s in Ioo (0 : ℝ) r, f s := by
  refine (operator_toLp_ae_eq_integral weightedVolterraKernel
    weightedVolterraKernel_memLp f).trans ?_
  filter_upwards with r
  have hkernel : (fun s => weightedVolterraKernel r s * f s) =
      (Ioo (0 : ℝ) r).indicator (fun s => (1 + r ^ 2)⁻¹ * f s) := by
    funext s
    by_cases hs : 0 < s ∧ s < r <;>
      simp [weightedVolterraKernel, Set.indicator, Set.mem_Ioo, hs]
  rw [hkernel, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo]
  have hinter : Ioo (0 : ℝ) r ∩ Ioi 0 = Ioo 0 r :=
    inter_eq_left.mpr (fun _ hs => hs.1)
  rw [hinter, integral_const_mul]

/-- The actual adjoint has the weighted tail-integral representative. -/
theorem weightedVolterraOperator_adjoint_ae_pointwise
    (f : RealL2 halfLineMeasure) :
    (ContinuousLinearMap.adjoint weightedVolterraOperator f : ℝ → ℝ) =ᵐ[
      halfLineMeasure] fun s => ∫ r in Ioi s, (1 + r ^ 2)⁻¹ * f r := by
  rw [weightedVolterraOperator_adjoint]
  refine (operator_toLp_ae_eq_integral
    (fun r s => weightedVolterraKernel s r)
    (kernel_transpose_memLp weightedVolterraKernel weightedVolterraKernel_memLp)
    f).trans ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hkernel : (fun r => weightedVolterraKernel r s * f r) =
      (Ioi s).indicator (fun r => (1 + r ^ 2)⁻¹ * f r) := by
    funext r
    by_cases hr : s < r <;>
      simp [weightedVolterraKernel, Set.indicator, Set.mem_Ioi,
        show 0 < s from hs, hr]
  rw [hkernel, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have hinter : Ioi s ∩ Ioi (0 : ℝ) = Ioi s := by
    apply inter_eq_left.mpr
    intro r hr
    change 0 < r
    exact lt_trans (show 0 < s from hs) (show s < r from hr)
  rw [hinter]

end HBL.Modulation.Monopole
