import HBL.TypeIIDynamicSelection.ActualHartreeMatchedKummerInteriorSourceBound
import Mathlib.Tactic

/-!
# Global-bubble pointwise envelope on the ACTUAL physical Kummer Green region

The genuine matched origin Kummer solution on [A*a,A*b] is controlled by
the same original Hartree Kummer source F and the same left Fredholm
Cauchy jet U,DU. Compatibility kills the singular homogeneous mode.
No upper-boundary-jet or independently chosen Green amplitude is assumed.

The geometry of the true physical interval converts the source-driven
uniform Kummer amplitude E into a bubble envelope with factor (1+A*b).
This is the missing Green-region analogue of the already strict
repair-annulus bubble envelope, needed for *all* full nonlocal Hartree
cross-density terms rather than only the compact outer replacement.

This is a fixed-slice source-to-field estimate. Uniform-in-time decay
still requires the actual moving basis constant, source and left-jet
orders to be proved from the same PDE orbit; no 9/4 profile is asserted.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation

theorem actual_Hartree_matched_physical_Green_bubble_from_source
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (A a b C M : ℝ)
    (hA : 0 < A) (ha : 0 < a) (hab : a ≤ b)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M)
    (U DU : ℂ)
    (hzero : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (y : ℝ) (hy : y ∈ Icc (A * a) (A * b)) :
    ‖actualOriginMatchedKummerPullback K A a b F U DU y‖ ≤
      (1 + A * b) *
        (2 * C ^ 3 * ((b - a) * M + ‖U‖ + ‖DU‖)) * bubble y := by
  let E : ℝ := 2 * C ^ 3 * ((b - a) * M + ‖U‖ + ‖DU‖)
  have hb : 0 ≤ b := ha.le.trans hab
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hy0 : 0 ≤ y := (mul_pos hA ha).le.trans hy.1
  have hyNorm : y / A ∈ Icc a b := by
    constructor
    · apply (le_div_iff₀ hA).2
      simpa only [mul_comm] using hy.1
    · apply (div_le_iff₀ hA).2
      simpa only [mul_comm] using hy.2
  have hInterior :=
    actual_Hartree_matched_Kummer_interior_from_source_and_left_jet
      K a b C M hC hM hK hab F hF U DU hzero (y / A) hyNorm
  have hValue : ‖actualOriginMatchedKummerPullback K A a b F U DU y‖ ≤ E := by
    change ‖actualOriginMatchedKummerValue K a b F U DU (y / A)‖ ≤ E
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans hInterior
  have hGeom : Real.sqrt (1 + y ^ 2) ≤ 1 + y := by
    calc
      _ ≤ Real.sqrt ((1 + y) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [hy0])
      _ = 1 + y := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos (by linarith)]
  have hRoot : 0 < Real.sqrt (1 + y ^ 2) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hUpper : Real.sqrt (1 + y ^ 2) ≤ 1 + A * b := by
    linarith [hGeom, hy.2]
  have hBubble : 1 ≤ (1 + A * b) * bubble y := by
    change 1 ≤ (1 + A * b) / Real.sqrt (1 + y ^ 2)
    exact (le_div_iff₀ hRoot).2 (by simpa only [one_mul] using hUpper)
  calc
    ‖actualOriginMatchedKummerPullback K A a b F U DU y‖ ≤ E := hValue
    _ = E * 1 := by ring
    _ ≤ E * ((1 + A * b) * bubble y) :=
      mul_le_mul_of_nonneg_left hBubble hE
    _ = (1 + A * b) * E * bubble y := by ring
    _ = (1 + A * b) *
        (2 * C ^ 3 * ((b - a) * M + ‖U‖ + ‖DU‖)) * bubble y := rfl

end HBL.TypeIIDynamicSelection
