import HBL.LogKernelHilbertSchmidt
import HBL.WeightedFreeGreen

/-!
The weighted Hartree part of the zero-energy Birman--Schwinger reduction.

Conjugating a half-line unknown by `q(r) = (1+r²)x(r)` changes the nonlocal
Hartree kernel from two factors of `W³` to two factors of `W`.  This file
proves directly that the resulting logarithmic kernel is still in product
L2, realizes it as a bounded operator, and proves compactness.  Symmetry of
the kernel is recorded separately; no self-adjointness claim is used here.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- Squared radial weight of one conjugated Hartree factor. -/
def birmanSquareWeight (r : ℝ) : ℝ := bubble r ^ 2

/-- Its square-root moment, needed at the logarithmic diagonal. -/
def birmanSquareSqrtWeight (r : ℝ) : ℝ :=
  Real.sqrt r * birmanSquareWeight r

theorem birmanSquareWeight_nonneg (r : ℝ) :
    0 ≤ birmanSquareWeight r := by
  unfold birmanSquareWeight
  positivity

theorem birmanSquareSqrtWeight_nonneg (r : ℝ) :
    0 ≤ birmanSquareSqrtWeight r := by
  unfold birmanSquareSqrtWeight
  exact mul_nonneg (Real.sqrt_nonneg r) (birmanSquareWeight_nonneg r)

theorem birmanSquareWeight_closed (r : ℝ) :
    birmanSquareWeight r = (1 + r ^ 2)⁻¹ := by
  unfold birmanSquareWeight bubble
  rw [inv_pow]
  congr 1
  exact Real.sq_sqrt (by positivity)

theorem birmanSquareWeight_continuous :
    Continuous birmanSquareWeight := by
  unfold birmanSquareWeight
  exact bubble_contDiff_infty.continuous.pow 2

theorem birmanSquareSqrtWeight_continuous :
    Continuous birmanSquareSqrtWeight := by
  unfold birmanSquareSqrtWeight
  exact Real.continuous_sqrt.mul birmanSquareWeight_continuous

theorem birmanSquareWeight_integrable :
    Integrable birmanSquareWeight := by
  refine integrable_inv_one_add_sq.congr ?_
  filter_upwards with r
  exact (birmanSquareWeight_closed r).symm

theorem birmanSquareSqrtWeight_le_rpow
    (r : ℝ) (hr : 1 < r) :
    birmanSquareSqrtWeight r ≤ r ^ (-(3 / 2 : ℝ)) := by
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  rw [birmanSquareSqrtWeight, birmanSquareWeight_closed, inv_eq_one_div]
  calc
    Real.sqrt r * (1 / (1 + r ^ 2)) =
        Real.sqrt r / (1 + r ^ 2) := by ring
    _ ≤ Real.sqrt r / r ^ 2 := by
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg r)
        (sq_pos_of_pos hrpos) (by linarith)
    _ = r ^ (-(3 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      calc
        r ^ (1 / 2 : ℝ) / r ^ 2 =
            r ^ (1 / 2 : ℝ) / r ^ (2 : ℝ) := by
              norm_num [Real.rpow_natCast]
        _ = r ^ ((1 / 2 : ℝ) - 2) := by rw [Real.rpow_sub hrpos]
        _ = r ^ (-(3 / 2 : ℝ)) := by norm_num

theorem birmanSquareSqrtWeight_integrable :
    Integrable birmanSquareSqrtWeight := by
  have hcoreOn : IntegrableOn birmanSquareSqrtWeight (Icc (0 : ℝ) 1) :=
    birmanSquareSqrtWeight_continuous.integrableOn_Icc
  have hcore := hcoreOn.integrable_indicator measurableSet_Icc
  have hpow : IntegrableOn
      (fun r : ℝ => r ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have htailOn : IntegrableOn birmanSquareSqrtWeight (Ioi 1) := by
    refine hpow.mono'
      birmanSquareSqrtWeight_continuous.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs,
      abs_of_nonneg (birmanSquareSqrtWeight_nonneg r)]
    exact birmanSquareSqrtWeight_le_rpow r hr
  have htail := htailOn.integrable_indicator measurableSet_Ioi
  refine (hcore.add htail).congr
    (Filter.Eventually.of_forall fun r => ?_)
  by_cases hr0 : 0 ≤ r
  · by_cases hr1 : r ≤ 1
    · simp [Set.indicator, hr0, hr1, not_lt_of_ge hr1]
    · have h1r : 1 < r := lt_of_not_ge hr1
      simp [Set.indicator, hr0, hr1, h1r]
  · have hsqrt : Real.sqrt r = 0 :=
      Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hr0)
    have hr1 : r ≤ 1 := le_trans (le_of_not_ge hr0) (by norm_num)
    simp [Set.indicator, hr0, hr1, birmanSquareSqrtWeight, hsqrt]

theorem birmanSquareWeight_norm_le_one (r : ℝ) :
    ‖birmanSquareWeight r‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (birmanSquareWeight_nonneg r),
    birmanSquareWeight_closed]
  exact (inv_le_one₀ (by positivity : 0 < 1 + r ^ 2)).2
    (by nlinarith [sq_nonneg r])

theorem birmanSquareSqrtWeight_norm_le_one (r : ℝ) :
    ‖birmanSquareSqrtWeight r‖ ≤ 1 := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg (birmanSquareSqrtWeight_nonneg r)]
  by_cases hr : 0 ≤ r
  · have hsle : Real.sqrt r ≤ 1 + r ^ 2 := by
      by_cases h1 : r ≤ 1
      · have hs : Real.sqrt r ≤ 1 := by
          nlinarith [Real.sqrt_nonneg r, Real.sq_sqrt hr]
        nlinarith [sq_nonneg r]
      · have hs : Real.sqrt r ≤ r := by
          nlinarith [Real.sqrt_nonneg r, Real.sq_sqrt hr]
        nlinarith [sq_nonneg r]
    rw [birmanSquareSqrtWeight, birmanSquareWeight_closed]
    calc
      Real.sqrt r * (1 + r ^ 2)⁻¹ ≤
          (1 + r ^ 2) * (1 + r ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hsle (by positivity)
      _ = 1 := by field_simp
  · have hsqrt : Real.sqrt r = 0 :=
      Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hr)
    simp [birmanSquareSqrtWeight, hsqrt]

/-- Nonlocal kernel after the weight `q(r)=(1+r²)x(r)`. -/
def weightedHartreeKernel (r rho : ℝ) : ℝ :=
  8 * Real.pi * hartreeKappa * bubble r * bubble rho *
    hartreeRadialLog r rho

theorem weightedHartreeKernel_symm (r rho : ℝ) :
    weightedHartreeKernel r rho = weightedHartreeKernel rho r := by
  unfold weightedHartreeKernel hartreeRadialLog
  rw [add_comm r rho, abs_sub_comm r rho]
  ring

theorem weightedHartreeKernel_uncurry_measurable :
    Measurable (Function.uncurry weightedHartreeKernel) := by
  unfold Function.uncurry weightedHartreeKernel hartreeRadialLog bubble
  measurability

theorem weightedHartreeKernel_sq_integrable :
    Integrable (fun p : ℝ × ℝ => weightedHartreeKernel p.1 p.2 ^ 2)
      (halfLineMeasure.prod halfLineMeasure) := by
  unfold weightedHartreeKernel
  exact product_log_kernel_sq_integrable
    bubble birmanSquareWeight birmanSquareSqrtWeight
    (8 * Real.pi * hartreeKappa)
    birmanSquareWeight_nonneg birmanSquareSqrtWeight_nonneg
    birmanSquareWeight_integrable birmanSquareSqrtWeight_integrable
    birmanSquareWeight_norm_le_one birmanSquareSqrtWeight_norm_le_one
    (fun r => rfl) (fun r _ => by
      rfl)
    weightedHartreeKernel_uncurry_measurable

theorem weightedHartreeKernel_memLp_two :
    MemLp (Function.uncurry weightedHartreeKernel) 2
      (halfLineMeasure.prod halfLineMeasure) := by
  apply (memLp_two_iff_integrable_sq
    weightedHartreeKernel_uncurry_measurable.aestronglyMeasurable).2
  exact weightedHartreeKernel_sq_integrable

/-- Product-L2 realization of the conjugated Hartree kernel. -/
def weightedHartreeKernelL2 : RealKernelL2 halfLineMeasure :=
  weightedHartreeKernel_memLp_two.toLp
    (Function.uncurry weightedHartreeKernel)

theorem weightedHartreeKernelL2_ae :
    (weightedHartreeKernelL2 : ℝ × ℝ → ℝ) =ᵐ[
      halfLineMeasure.prod halfLineMeasure]
      Function.uncurry weightedHartreeKernel :=
  weightedHartreeKernel_memLp_two.coeFn_toLp

/-- Bounded L2 operator represented by the conjugated Hartree kernel. -/
def weightedHartreeOperator :
    RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure :=
  operator weightedHartreeKernelL2

theorem weightedHartreeOperator_kernel_certificate :
    IsHilbertSchmidtKernelOperator weightedHartreeOperator
      weightedHartreeKernelL2 :=
  operator_isHilbertSchmidtKernelOperator weightedHartreeKernelL2

theorem weightedHartreeKernel_inner_tensor_swap
    (f g : RealL2 halfLineMeasure) :
    inner ℝ weightedHartreeKernelL2 (tensor g f) =
      inner ℝ weightedHartreeKernelL2 (tensor f g) := by
  rw [L2.inner_def, L2.inner_def]
  have hleft :
      (fun p : ℝ × ℝ => inner ℝ (weightedHartreeKernelL2 p)
        (tensor g f p)) =ᵐ[halfLineMeasure.prod halfLineMeasure]
      fun p => weightedHartreeKernel p.1 p.2 * (g p.1 * f p.2) := by
    filter_upwards [weightedHartreeKernelL2_ae, tensor_ae g f] with p hK ht
    rw [hK, ht, Real.inner_apply]
    change weightedHartreeKernel p.1 p.2 * (g p.1 * f p.2) = _
    rfl
  have hright :
      (fun p : ℝ × ℝ => inner ℝ (weightedHartreeKernelL2 p)
        (tensor f g p)) =ᵐ[halfLineMeasure.prod halfLineMeasure]
      fun p => weightedHartreeKernel p.1 p.2 * (f p.1 * g p.2) := by
    filter_upwards [weightedHartreeKernelL2_ae, tensor_ae f g] with p hK ht
    rw [hK, ht, Real.inner_apply]
    change weightedHartreeKernel p.1 p.2 * (f p.1 * g p.2) = _
    rfl
  rw [integral_congr_ae hleft, integral_congr_ae hright]
  calc
    (∫ p : ℝ × ℝ, weightedHartreeKernel p.1 p.2 * (g p.1 * f p.2)
        ∂(halfLineMeasure.prod halfLineMeasure)) =
        ∫ p : ℝ × ℝ,
          (fun q : ℝ × ℝ =>
            weightedHartreeKernel q.1 q.2 * (g q.1 * f q.2)) p.swap
          ∂(halfLineMeasure.prod halfLineMeasure) := by
      symm
      simpa only using (MeasureTheory.integral_prod_swap
        (μ := halfLineMeasure) (ν := halfLineMeasure)
        (fun q : ℝ × ℝ =>
          weightedHartreeKernel q.1 q.2 * (g q.1 * f q.2)))
    _ = ∫ p : ℝ × ℝ,
        weightedHartreeKernel p.1 p.2 * (f p.1 * g p.2)
        ∂(halfLineMeasure.prod halfLineMeasure) := by
      apply integral_congr_ae
      filter_upwards with p
      change weightedHartreeKernel p.2 p.1 * (g p.2 * f p.1) =
        weightedHartreeKernel p.1 p.2 * (f p.1 * g p.2)
      rw [weightedHartreeKernel_symm]
      ring

/-- The symmetric conjugated Hartree kernel realizes a self-adjoint
operator. -/
theorem weightedHartreeOperator_selfAdjoint :
    IsSelfAdjoint weightedHartreeOperator := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  calc
    inner ℝ (weightedHartreeOperator f) g =
        inner ℝ weightedHartreeKernelL2 (tensor g f) := inner_operator _ _ _
    _ = inner ℝ weightedHartreeKernelL2 (tensor f g) :=
      weightedHartreeKernel_inner_tensor_swap f g
    _ = inner ℝ (weightedHartreeOperator g) f :=
      (inner_operator _ _ _).symm
    _ = inner ℝ f (weightedHartreeOperator g) := real_inner_comm _ _

theorem weightedHartreeOperator_compact :
    IsCompactOperator weightedHartreeOperator :=
  operator_isCompactOperator weightedHartreeKernelL2

/-- The conjugated real-channel potential: the local coefficient is `9`,
and the second summand is the conjugated nonlocal Hartree operator. -/
def weightedPotentialOperator :
    RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure :=
  (9 : ℝ) • ContinuousLinearMap.id ℝ (RealL2 halfLineMeasure) +
    weightedHartreeOperator

/-- The complete conjugated potential is self-adjoint. -/
theorem weightedPotentialOperator_selfAdjoint :
    IsSelfAdjoint weightedPotentialOperator := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  unfold weightedPotentialOperator
  rw [ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.coe_id]
  have hid :
      (LinearMap.id : RealL2 halfLineMeasure →ₗ[ℝ]
        RealL2 halfLineMeasure).IsSymmetric := LinearMap.IsSymmetric.one
  have hlocal :
      ((9 : ℝ) • (LinearMap.id : RealL2 halfLineMeasure →ₗ[ℝ]
        RealL2 halfLineMeasure)).IsSymmetric := hid.smul (by simp)
  have hhartree :
      (weightedHartreeOperator : RealL2 halfLineMeasure →ₗ[ℝ]
        RealL2 halfLineMeasure).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedHartreeOperator_selfAdjoint
  exact hlocal.add hhartree

/-- Compact Birman--Schwinger operator obtained by applying the weighted
free Dirichlet Green operator to the complete conjugated potential. -/
def weightedBirmanSchwingerOperator :
    RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure :=
  weightedFreeGreenOperator ∘L weightedPotentialOperator

theorem weightedBirmanSchwingerOperator_compact :
    IsCompactOperator weightedBirmanSchwingerOperator := by
  unfold weightedBirmanSchwingerOperator
  exact weightedFreeGreenOperator_compact.comp_clm weightedPotentialOperator

/-- The actual adjoint of the generally non-self-adjoint
Birman--Schwinger composite reverses its two self-adjoint factors. -/
theorem weightedBirmanSchwingerOperator_adjoint :
    ContinuousLinearMap.adjoint weightedBirmanSchwingerOperator =
      weightedPotentialOperator ∘L weightedFreeGreenOperator := by
  unfold weightedBirmanSchwingerOperator
  rw [ContinuousLinearMap.adjoint_comp,
    weightedPotentialOperator_selfAdjoint.adjoint_eq,
    weightedFreeGreenOperator_selfAdjoint.adjoint_eq]

/-- Once radial nondegeneracy identifies the fixed space of the actual
Birman--Schwinger operator, the reversed-factor adjoint formula identifies
its fixed space exactly, without an injectivity assumption on either
factor. -/
theorem weightedBirmanSchwinger_adjoint_fixed_mem_span_iff
    (x0 y : RealL2 halfLineMeasure)
    (hfixed : ∀ x : RealL2 halfLineMeasure,
      weightedBirmanSchwingerOperator x = x ↔
        x ∈ Submodule.span ℝ {x0}) :
    ContinuousLinearMap.adjoint weightedBirmanSchwingerOperator y = y ↔
      y ∈ Submodule.span ℝ {weightedPotentialOperator x0} := by
  constructor
  · intro hy
    have hPG :
        weightedPotentialOperator (weightedFreeGreenOperator y) = y := by
      calc
        weightedPotentialOperator (weightedFreeGreenOperator y) =
            (weightedPotentialOperator ∘L weightedFreeGreenOperator) y := rfl
        _ = ContinuousLinearMap.adjoint weightedBirmanSchwingerOperator y :=
          congrArg (fun T : RealL2 halfLineMeasure →L[ℝ]
            RealL2 halfLineMeasure => T y)
            weightedBirmanSchwingerOperator_adjoint.symm
        _ = y := hy
    have hGy :
        weightedBirmanSchwingerOperator (weightedFreeGreenOperator y) =
          weightedFreeGreenOperator y := by
      unfold weightedBirmanSchwingerOperator
      rw [ContinuousLinearMap.comp_apply, hPG]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      ((hfixed (weightedFreeGreenOperator y)).mp hGy)
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    calc
      c • weightedPotentialOperator x0 =
          weightedPotentialOperator (c • x0) :=
        (weightedPotentialOperator.map_smul c x0).symm
      _ = weightedPotentialOperator (weightedFreeGreenOperator y) := by
        rw [hc]
      _ = y := hPG
  · intro hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hx0 : weightedBirmanSchwingerOperator x0 = x0 :=
      (hfixed x0).mpr (Submodule.mem_span_singleton_self x0)
    have hGP : weightedFreeGreenOperator (weightedPotentialOperator x0) = x0 := by
      simpa only [weightedBirmanSchwingerOperator,
        ContinuousLinearMap.comp_apply] using hx0
    rw [weightedBirmanSchwingerOperator_adjoint]
    simp only [ContinuousLinearMap.comp_apply, map_smul]
    rw [hGP]

/-- Kernel form of the preceding fixed-space identification.  The
hypothesis is precisely the radial nondegeneracy input still to be bridged
from the differential Hartree operator. -/
theorem weightedBirmanSchwinger_adjointKernel_eq_span
    (x0 : RealL2 halfLineMeasure)
    (hfixed : ∀ x : RealL2 halfLineMeasure,
      weightedBirmanSchwingerOperator x = x ↔
        x ∈ Submodule.span ℝ {x0}) :
    (ContinuousLinearMap.id ℝ (RealL2 halfLineMeasure) -
      ContinuousLinearMap.adjoint weightedBirmanSchwingerOperator).ker =
        Submodule.span ℝ {weightedPotentialOperator x0} := by
  ext y
  rw [LinearMap.mem_ker]
  change y - ContinuousLinearMap.adjoint weightedBirmanSchwingerOperator y = 0 ↔
    y ∈ Submodule.span ℝ {weightedPotentialOperator x0}
  rw [sub_eq_zero, eq_comm]
  exact weightedBirmanSchwinger_adjoint_fixed_mem_span_iff x0 y hfixed

end HBL.Modulation.Monopole
