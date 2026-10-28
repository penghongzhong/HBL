import HBL.WeightedGreenEigenClassification
import HBL.FredholmCokernelAlternative
import Mathlib.Tactic

/-!
# Phase-channel Fredholm core

For the local H_- channel after endpoint conjugation the compact
Birman--Schwinger part is exactly 3 G_w, where G_w is the already
constructed weighted free Green operator.  The positive Green spectrum
therefore gives the full kernel of I - 3 G_w.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

def weightedPhaseBirman :
    RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure :=
  (3 : ℝ) • weightedFreeGreenOperator

theorem weightedPhaseBirman_compact :
    IsCompactOperator weightedPhaseBirman := by
  exact weightedFreeGreenOperator_compact.smul (3 : ℝ)

theorem weightedPhaseBirman_selfAdjoint :
    IsSelfAdjoint weightedPhaseBirman := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℝ ((3 : ℝ) • weightedFreeGreenOperator x) y =
    inner ℝ x ((3 : ℝ) • weightedFreeGreenOperator y)
  rw [real_inner_smul_left, real_inner_smul_right]
  exact congrArg (fun t : ℝ => 3 * t)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedFreeGreenOperator_selfAdjoint x y)

theorem weightedPhaseBirman_sine_one_fixed :
    weightedPhaseBirman (weightedHartreeSineModeL2 1) =
      weightedHartreeSineModeL2 1 := by
  unfold weightedPhaseBirman
  rw [ContinuousLinearMap.smul_apply,
    weightedFreeGreenOperator_sineMode 1 (by omega)]
  rw [smul_smul]
  norm_num

theorem weightedPhaseFredholm_kernel_eq_sine_span :
    (1 - weightedPhaseBirman).ker =
      Submodule.span ℝ {weightedHartreeSineModeL2 1} := by
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    have hthree :
        (3 : ℝ) • weightedFreeGreenOperator x = x := by
      change x - (3 : ℝ) • weightedFreeGreenOperator x = 0 at hx
      exact (sub_eq_zero.mp hx).symm
    have hg :
        weightedFreeGreenOperator x = (1 / 3 : ℝ) • x := by
      calc
        weightedFreeGreenOperator x =
            (1 / 3 : ℝ) • ((3 : ℝ) • weightedFreeGreenOperator x) := by
              module
        _ = (1 / 3 : ℝ) • x := by rw [hthree]
    have hcoeff :
        (1 / (4 * ((1 : ℕ) : ℝ) ^ 2 - 1) : ℝ) = (1 / 3 : ℝ) := by
      norm_num
    exact (weightedFreeGreen_sine_eigen_iff 1 (by omega) x).1
      (by rw [hcoeff]; exact hg)
  · intro hx
    have hg := (weightedFreeGreen_sine_eigen_iff 1 (by omega) x).2 hx
    change x - (3 : ℝ) • weightedFreeGreenOperator x = 0
    rw [hg]
    module

theorem weightedPhaseFredholm_kernel_finrank :
    Module.finrank ℝ (1 - weightedPhaseBirman).ker = 1 := by
  rw [weightedPhaseFredholm_kernel_eq_sine_span]
  exact finrank_span_singleton (weightedHartreeSineModeL2_ne_zero 1 (by omega))

theorem weightedPhaseFredholm_adjoint_eq :
    ContinuousLinearMap.adjoint (1 - weightedPhaseBirman) =
      1 - weightedPhaseBirman := by
  have hself : IsSelfAdjoint
      (1 - weightedPhaseBirman : RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change inner ℝ (x - weightedPhaseBirman x) y =
      inner ℝ x (y - weightedPhaseBirman y)
    rw [inner_sub_left, inner_sub_right]
    have hsym :
        inner ℝ (weightedPhaseBirman x) y =
          inner ℝ x (weightedPhaseBirman y) :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        weightedPhaseBirman_selfAdjoint) x y
    exact congrArg (fun v : ℝ => inner ℝ x y - v) hsym
  exact hself

theorem weightedPhaseFredholm_adjointKernel_eq_sine_span :
    (ContinuousLinearMap.adjoint (1 - weightedPhaseBirman)).ker =
      Submodule.span ℝ {weightedHartreeSineModeL2 1} := by
  rw [weightedPhaseFredholm_adjoint_eq,
    weightedPhaseFredholm_kernel_eq_sine_span]

#print axioms weightedPhaseBirman_compact
#print axioms weightedPhaseFredholm_kernel_eq_sine_span
#print axioms weightedPhaseFredholm_adjointKernel_eq_sine_span

end HBL.Modulation.Monopole
