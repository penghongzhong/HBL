import HBL.KinematicSliceDefinitions

/-!
A direct terminal-amplitude normalization for the actual affine clock.
The reciprocal tail is the scalar synchronization equation.  This formula
retains a common terminal amplitude and makes the initial-slice identity
exact, without an implicit-function theorem for the scale itself.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Kinematic

def sliceBeta (A : ℝ) : ℝ := (A + 1) / (2 * A)

def sliceTailFrom (A s₀ κ : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in Ioi s, sliceIntegrand A s₀ κ h t

def sliceLambda (A s₀ κ Λ : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  (Λ * s ^ sliceBeta A) * Real.sqrt (sliceClock A s₀ κ h s / (A * s)) *
    Real.exp (-(sliceTailFrom A s₀ κ h s) / 2)

def sliceReferenceTime (A Λ s : ℝ) : ℝ :=
  A * s / (Λ * s ^ sliceBeta A) ^ 2

def slicePhysicalTime (A s₀ κ Λ : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  sliceClock A s₀ κ h s / sliceLambda A s₀ κ Λ h s ^ 2

theorem sliceLambda_pos {A s₀ κ Λ s : ℝ} {h : ℝ → ℝ}
    (hA : 0 < A) (hs : 0 < s) (hΛ : 0 < Λ)
    (hq : 0 < sliceClock A s₀ κ h s) :
    0 < sliceLambda A s₀ κ Λ h s := by
  unfold sliceLambda
  exact mul_pos (mul_pos (mul_pos hΛ (Real.rpow_pos_of_pos hs _))
    (Real.sqrt_pos.2 (div_pos hq (mul_pos hA hs)))) (Real.exp_pos _)

theorem sliceLambda_sq {A s₀ κ Λ s : ℝ} {h : ℝ → ℝ}
    (hA : 0 < A) (hs : 0 < s)
    (hq : 0 < sliceClock A s₀ κ h s) :
    sliceLambda A s₀ κ Λ h s ^ 2 =
      (Λ * s ^ sliceBeta A) ^ 2 * (sliceClock A s₀ κ h s / (A * s)) *
        Real.exp (-sliceTailFrom A s₀ κ h s) := by
  have hexp : Real.exp (-(sliceTailFrom A s₀ κ h s) / 2) ^ 2 =
      Real.exp (-sliceTailFrom A s₀ κ h s) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold sliceLambda
  rw [mul_pow, mul_pow, Real.sq_sqrt (div_pos hq (mul_pos hA hs)).le, hexp]

theorem slicePhysicalTime_eq_reference_mul_exp
    {A s₀ κ Λ s : ℝ} {h : ℝ → ℝ}
    (hA : 0 < A) (hs : 0 < s) (hΛ : 0 < Λ)
    (hq : 0 < sliceClock A s₀ κ h s) :
    slicePhysicalTime A s₀ κ Λ h s =
      sliceReferenceTime A Λ s * Real.exp (sliceTailFrom A s₀ κ h s) := by
  have hb : Λ * s ^ sliceBeta A ≠ 0 :=
    (mul_pos hΛ (Real.rpow_pos_of_pos hs _)).ne'
  unfold slicePhysicalTime sliceReferenceTime
  rw [sliceLambda_sq hA hs hq, Real.exp_neg]
  field_simp [hb, hA.ne', hs.ne', hq.ne']

theorem synchronized_slice_iff_tail_zero
    {A s₀ κ Λ : ℝ} {h : ℝ → ℝ}
    (hA : 0 < A) (hs₀ : 0 < s₀) (hΛ : 0 < Λ)
    (hq : 0 < sliceClock A s₀ κ h s₀) :
    slicePhysicalTime A s₀ κ Λ h s₀ = sliceReferenceTime A Λ s₀ ↔
      sliceTail A s₀ κ h = 0 := by
  have ht : sliceReferenceTime A Λ s₀ ≠ 0 := by
    unfold sliceReferenceTime
    exact (div_pos (mul_pos hA hs₀)
      (sq_pos_of_pos (mul_pos hΛ (Real.rpow_pos_of_pos hs₀ _)))).ne'
  rw [slicePhysicalTime_eq_reference_mul_exp hA hs₀ hΛ hq]
  change sliceReferenceTime A Λ s₀ * Real.exp (sliceTail A s₀ κ h) =
      sliceReferenceTime A Λ s₀ ↔ _
  rw [mul_eq_left₀ ht, Real.exp_eq_one_iff]

end HBL.Kinematic
