import HBL.KinematicSliceDynamics
import Mathlib.Tactic

/-!
# The physical Kummer scale has an actual O(s^{-1}) relative speed

For the synchronized slice clock
  q(s)=A s+kappa+4 integral h,
set a(s)=sqrt(q(s)).  The existing clock derivative and trapped linear lower
bound give an exact derivative for a and a relative-speed bound C/s.

This is much weaker than, and independent of, the final Type-II asymptotic
rate.  It supplies the scale-speed input of the physical Kummer repair time
derivative.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

def actualKummerScaleFromSliceClock
    (A s0 kappa : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.sqrt (HBL.Kinematic.sliceClock A s0 kappa h s)

theorem actual_Kummer_scale_from_slice_clock_hasDerivAt
    {A s0 kappa s : ℝ} (h : ℝ → ℝ)
    (hh : ContinuousOn h (Ici s0))
    (hs : s0 < s)
    (hq : 0 < HBL.Kinematic.sliceClock A s0 kappa h s) :
    HasDerivAt
      (actualKummerScaleFromSliceClock A s0 kappa h)
      ((A + 4 * h s) /
        (2 * actualKummerScaleFromSliceClock A s0 kappa h s)) s := by
  have hqDeriv :=
    HBL.Kinematic.sliceClock_hasDerivAt
      (A := A) (s₀ := s0) (κ := kappa) h hh hs
  have hsqrt := hqDeriv.sqrt hq.ne'
  change HasDerivAt
    (fun y => Real.sqrt (HBL.Kinematic.sliceClock A s0 kappa h y))
    ((A + 4 * h s) /
      (2 * Real.sqrt (HBL.Kinematic.sliceClock A s0 kappa h s))) s
  exact hsqrt

/-- The true square-root clock scale has relative speed O(1/s).
No limiting modulation exponent or final concentration law is used. -/
theorem actual_Kummer_scale_relative_speed_from_slice_clock
    {A s0 kappa delta H s : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs0 : 1 ≤ s0)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hH : 0 ≤ H)
    (hh : ContinuousOn h (Ici s0))
    (hbound : ∀ t : ℝ, s0 ≤ t → |h t| ≤ H * t ^ (-delta))
    (hsmall : (4 * H / (1 - delta)) * s0 ^ (-delta) ≤ A / 4)
    (hkappa : |kappa| ≤ A * s0 / 4)
    (hs : s0 < s) :
    let a := actualKummerScaleFromSliceClock A s0 kappa h s
    let adot := (A + 4 * h s) / (2 * a)
    HasDerivAt
      (actualKummerScaleFromSliceClock A s0 kappa h) adot s ∧
    0 < a ∧
    |adot| / a ≤ ((A + 4 * H) / A) * s ^ (-1 : ℝ) := by
  dsimp only
  let q : ℝ := HBL.Kinematic.sliceClock A s0 kappa h s
  let a : ℝ := actualKummerScaleFromSliceClock A s0 kappa h s
  let adot : ℝ := (A + 4 * h s) / (2 * a)
  have hs0pos : 0 < s0 := lt_of_lt_of_le zero_lt_one hs0
  have hsone : 1 ≤ s := hs0.trans hs.le
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hsone
  have hClock :=
    HBL.Kinematic.sliceClock_linear_bounds
      (A := A) (s₀ := s0) (κ := kappa) (δ := delta) (H := H)
      h hA hs0pos hdelta hdelta1 hH hbound hsmall hkappa hs.le
  have hqpos : 0 < q := by
    dsimp [q]
    have hlow := hClock.1
    have : 0 < A / 2 * s := mul_pos (by positivity) hspos
    exact this.trans_le hlow
  have haPos : 0 < a := by
    dsimp [a, actualKummerScaleFromSliceClock, q] at hqpos ⊢
    exact Real.sqrt_pos.2 hqpos
  have hDeriv :
      HasDerivAt
        (actualKummerScaleFromSliceClock A s0 kappa h) adot s := by
    dsimp [adot, a, q]
    exact actual_Kummer_scale_from_slice_clock_hasDerivAt
      h hh hs hqpos
  have hsPow : s ^ (-delta) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hsone (by linarith)
  have hhS : |h s| ≤ H := by
    calc
      |h s| ≤ H * s ^ (-delta) := hbound s hs.le
      _ ≤ H * 1 := mul_le_mul_of_nonneg_left hsPow hH
      _ = H := mul_one H
  have hnum : |A + 4 * h s| ≤ A + 4 * H := by
    calc
      |A + 4 * h s| ≤ |A| + |4 * h s| := abs_add_le _ _
      _ = A + 4 * |h s| := by
        rw [abs_of_pos hA, abs_mul]
        norm_num
      _ ≤ A + 4 * H := by linarith
  have hN : 0 ≤ A + 4 * H := by linarith
  have hqLow : A * s ≤ 2 * q := by
    dsimp [q]
    nlinarith [hClock.1]
  have hdenPos : 0 < A * s := mul_pos hA hspos
  have hsqrtSq : a ^ 2 = q := by
    dsimp [a, actualKummerScaleFromSliceClock, q]
    exact Real.sq_sqrt hqpos.le
  have hrelEq :
      |adot| / a = |A + 4 * h s| / (2 * q) := by
    dsimp [adot]
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) haPos)]
    rw [← hsqrtSq]
    field_simp [haPos.ne']
  have hfirst :
      |A + 4 * h s| / (2 * q) ≤
        (A + 4 * H) / (2 * q) := by
    exact (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * q)).2 hnum
  have hsecond :
      (A + 4 * H) / (2 * q) ≤
        (A + 4 * H) / (A * s) := by
    exact div_le_div_of_nonneg_left hN hdenPos hqLow
  have hfinal :
      (A + 4 * H) / (A * s) =
        ((A + 4 * H) / A) * s ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    field_simp [hA.ne', hspos.ne']
  refine ⟨hDeriv, haPos, ?_⟩
  rw [hrelEq]
  exact hfirst.trans (hsecond.trans_eq hfinal)

end HBL.TypeIIDynamicSelection
