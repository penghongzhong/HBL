import HBL.HartreeTailLeakage
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Finite annular action of the original Hartree kernel. This module
isolates scalar integration from the full normalized Fredholm construction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.AffineTail

private theorem exterior_inverse_square_integral
    (L U : ℝ) (hL : 0 < L) (hOrder : L ≤ U) :
    IntervalIntegrable (fun y : ℝ => y⁻¹ ^ 2) volume L U ∧
      (∫ y : ℝ in L..U, y⁻¹ ^ 2) = L⁻¹ - U⁻¹ := by
  have hP : ContinuousOn (fun y : ℝ => y⁻¹ ^ 2) (Icc L U) := by
    intro y hy
    exact ((hasDerivAt_inv (hL.trans_le hy.1).ne').continuousAt.pow 2).continuousWithinAt
  have hPI : IntervalIntegrable (fun y : ℝ => y⁻¹ ^ 2) volume L U :=
    hP.intervalIntegrable_of_Icc hOrder
  have hNo : (0 : ℝ) ∉ uIcc L U := notMem_uIcc_of_lt hL (hL.trans_le hOrder)
  have hIntegral := integral_zpow (a := L) (b := U)
    (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hNo⟩)
  refine ⟨hPI, ?_⟩
  calc
    (∫ y : ℝ in L..U, y⁻¹ ^ 2) = ∫ y : ℝ in L..U, y ^ (-2 : ℤ) := by
      apply intervalIntegral.integral_congr
      intro y _
      simp [zpow_neg, inv_pow]
    _ = (U ^ ((-2 : ℤ) + 1) - L ^ ((-2 : ℤ) + 1)) / ((-2 : ℤ) + 1) := hIntegral
    _ = -(U⁻¹ - L⁻¹) := by norm_num
    _ = L⁻¹ - U⁻¹ := by ring

private theorem exterior_inverse_square_majorant
    (L U A : ℝ) (hL : 0 < L) (hOrder : L ≤ U) (hA : 0 ≤ A)
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f (volume.restrict (uIoc L U)))
    (hPoint : ∀ y ∈ Icc L U, |f y| ≤ A * y⁻¹ ^ 2) :
    IntervalIntegrable f volume L U ∧ |∫ y in L..U, f y| ≤ A * L⁻¹ := by
  obtain ⟨hPI, hIntegral⟩ := exterior_inverse_square_integral L U hL hOrder
  have hMajor : IntervalIntegrable (fun y : ℝ => A * y⁻¹ ^ 2) volume L U := hPI.const_mul A
  have hInt : IntervalIntegrable f volume L U := by
    apply hMajor.mono_fun' hf
    rw [uIoc_of_le hOrder]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    simpa only [Real.norm_eq_abs] using hPoint y (Ioc_subset_Icc_self hy)
  refine ⟨hInt, ?_⟩
  calc
    |∫ y in L..U, f y| ≤ ∫ y in L..U, |f y| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (f := f) hOrder)
    _ ≤ ∫ y in L..U, A * y⁻¹ ^ 2 :=
      intervalIntegral.integral_mono_on hOrder hInt.abs hMajor hPoint
    _ = A * (L⁻¹ - U⁻¹) := by rw [intervalIntegral.integral_const_mul, hIntegral]
    _ ≤ A * L⁻¹ := mul_le_mul_of_nonneg_left
      (sub_le_self _ (inv_nonneg.mpr (hL.le.trans hOrder))) hA

private theorem exterior_quadratic_kernel_density
    (L r M y : ℝ) (hL : 0 < L) (hr : 0 < r) (hy : L ≤ y)
    (hsep : 2 * r ≤ L) (q : ℝ) (hq : |q| ≤ M * y ^ 2 / L) :
    |hartreeKernel r y * q| ≤
      (4 * |8 * Real.pi * hartreeKappa| * M * r * bubble r ^ 3 / L) * y⁻¹ ^ 2 := by
  have hyp : 0 < y := hL.trans_le hy
  have hk := hartreeKernel_separated_ordered y r hyp hr (hsep.trans hy)
  rw [hartreeKernel_symm y r, ← bubble_pow_three_eq_bracket] at hk
  rw [abs_mul]
  calc
    _ ≤ ((4 * |8 * Real.pi * hartreeKappa|) * y⁻¹ ^ 4 * r * bubble r ^ 3) *
        (M * y ^ 2 / L) := mul_le_mul hk hq (abs_nonneg _)
          (by unfold bubble; positivity)
    _ = _ := by field_simp [hyp.ne', hL.ne']

/-- Genuine finite-annulus Hartree integral bound for a quadratic radial
source. The bound is uniform in the upper endpoint U. -/
theorem actual_Hartree_quadratic_annulus_kernel_bound
    (L U r M : ℝ) (hL : 0 < L) (hOrder : L ≤ U) (hr : 0 < r)
    (hsep : 2 * r ≤ L) (hM : 0 ≤ M) (q : ℝ → ℝ)
    (hq : ContinuousOn q (Icc L U))
    (hBound : ∀ y ∈ Icc L U, |q y| ≤ M * y ^ 2 / L) :
    IntervalIntegrable (fun y => hartreeKernel r y * q y) volume L U ∧
      |∫ y in L..U, hartreeKernel r y * q y| ≤
        32 * Real.pi * hartreeKappa * M * r * bubble r ^ 3 / L ^ 2 := by
  let A := 4 * |8 * Real.pi * hartreeKappa| * M * r * bubble r ^ 3 / L
  have hA : 0 ≤ A := by dsimp [A]; unfold bubble; positivity
  have hKMeas : Measurable (fun y : ℝ => hartreeKernel r y) := by
    have hPair : Measurable (fun y : ℝ => (r, y)) :=
      measurable_const.prodMk measurable_id
    have hh := hartreeKernel_uncurry_measurable.comp hPair
    exact hh
  have hqI : IntervalIntegrable q volume L U := hq.intervalIntegrable_of_Icc hOrder
  have hqMeas : AEStronglyMeasurable q (volume.restrict (uIoc L U)) := by
    rw [uIoc_of_le hOrder]
    exact hqI.1.aestronglyMeasurable
  have hKm : AEStronglyMeasurable (fun y : ℝ => hartreeKernel r y)
      (volume.restrict (uIoc L U)) := hKMeas.aestronglyMeasurable
  have hProduct : AEStronglyMeasurable (fun y : ℝ => hartreeKernel r y * q y)
      (volume.restrict (uIoc L U)) := hKm.mul hqMeas
  have hBoth := exterior_inverse_square_majorant L U A hL hOrder hA
    (fun y => hartreeKernel r y * q y) hProduct
    (fun y hy => exterior_quadratic_kernel_density L r M y hL hr hy.1 hsep (q y) (hBound y hy))
  refine ⟨hBoth.1, hBoth.2.trans_eq ?_⟩
  dsimp [A]
  rw [abs_of_nonneg (show 0 ≤ 8 * Real.pi * hartreeKappa by unfold hartreeKappa; positivity)]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end HBL.TypeIIDynamicSelection
