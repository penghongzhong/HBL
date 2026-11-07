import HBL.TypeIIDynamicSelection.ActualHartreeSelectedSpeedDirectLipschitz
import Mathlib.Tactic

/-!
# Direct two-point Cramer estimate with BOTH compatibility columns moving

The locked HBL shooting problem varies its two retained threshold parameters.
The true coupled Fredholm--Kummer compatibility columns generally vary too.
A fixed-matrix source-only Lipschitz estimate is therefore insufficient.

Subtracting the TWO genuine exact Cramer cancellation identities supplies
a difference equation with the first full matrix; a second inverse is not
inserted. The resulting uniform estimate is derived from the existing
actual determinant and column budget, without differentiating parameters.
The PDE source/column difference estimates remain separate physical inputs.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

/-- Exact two-matrix compatibility difference with no dropped column
variation. Each p is uniquely selected by its own actual matrix. -/
theorem actual_real_Cramer_two_matrix_difference_cancel
    (b1 w1 b2 w2 Z1 Z2 : ℂ)
    (hdet1 : b1.re * w1.im - w1.re * b1.im ≠ 0)
    (hdet2 : b2.re * w2.im - w2.re * b2.im ≠ 0) :
    let p1 := actualRealCramerCorrection b1 w1 Z1
    let p2 := actualRealCramerCorrection b2 w2 Z2
    let F := Z1 - Z2 +
      (p2.1 : ℂ) * (b1 - b2) +
      (p2.2 : ℂ) * (w1 - w2)
    F + (((p1-p2).1 : ℝ) : ℂ) * b1 +
      (((p1-p2).2 : ℝ) : ℂ) * w1 = 0 := by
  dsimp only
  let p1 := actualRealCramerCorrection b1 w1 Z1
  let p2 := actualRealCramerCorrection b2 w2 Z2
  have h1 := actual_real_Cramer_correction_cancel b1 w1 Z1 hdet1
  have h2 := actual_real_Cramer_correction_cancel b2 w2 Z2 hdet2
  change Z1 + (p1.1 : ℂ) * b1 + (p1.2 : ℂ) * w1 = 0 at h1
  change Z2 + (p2.1 : ℂ) * b2 + (p2.2 : ℂ) * w2 = 0 at h2
  change
    (Z1 - Z2 + (p2.1 : ℂ) * (b1 - b2) +
      (p2.2 : ℂ) * (w1 - w2)) +
    ((((p1-p2).1 : ℝ) : ℂ)) * b1 +
    ((((p1-p2).2 : ℝ) : ℂ)) * w1 = 0
  have hSub1 : ((p1 - p2).1 : ℂ) = (p1.1 : ℂ) - (p2.1 : ℂ) := by
    change ((p1.1 - p2.1 : ℝ) : ℂ) = _
    push_cast
    ring
  have hSub2 : ((p1 - p2).2 : ℂ) = (p1.2 : ℂ) - (p2.2 : ℂ) := by
    change ((p1.2 - p2.2 : ℝ) : ℂ) = _
    push_cast
    ring
  rw [hSub1, hSub2]
  calc
    _ = (Z1 + (p1.1 : ℂ) * b1 + (p1.2 : ℂ) * w1) -
        (Z2 + (p2.1 : ℂ) * b2 + (p2.2 : ℂ) * w2) := by ring
    _ = 0 := by rw [h1, h2]; ring

/-- Actual two-column determinant inverse yields a difference estimate
without a Fréchet derivative, including the missing moving-column terms. -/
theorem actual_real_Cramer_two_matrix_difference_bound
    (a B : ℝ) (ha : 0 < a) (hB : 0 < B)
    (b1 w1 b2 w2 Z1 Z2 : ℂ)
    (hb1 : ‖b1‖ ≤ a * B ^ 2)
    (hw1 : ‖w1‖ ≤ a * B ^ 2)
    (hdet1 : a ^ 2 * B ^ 4 / 256 ≤
      b1.re * w1.im - w1.re * b1.im)
    (hdet2 : b2.re * w2.im - w2.re * b2.im ≠ 0) :
    let p1 := actualRealCramerCorrection b1 w1 Z1
    let p2 := actualRealCramerCorrection b2 w2 Z2
    ‖p1 - p2‖ ≤
      (1024 / (a * B ^ 2)) *
        (‖Z1 - Z2‖ + |p2.1| * ‖b1-b2‖ +
          |p2.2| * ‖w1-w2‖) := by
  dsimp only
  let p1 := actualRealCramerCorrection b1 w1 Z1
  let p2 := actualRealCramerCorrection b2 w2 Z2
  let d := p1 - p2
  let F := Z1 - Z2 + (p2.1 : ℂ) * (b1-b2) +
    (p2.2 : ℂ) * (w1-w2)
  have hdet1Ne :
      b1.re * w1.im - w1.re * b1.im ≠ 0 :=
    ((by positivity : 0 < a ^ 2 * B ^ 4 / 256).trans_le hdet1).ne'
  have hCancel :=
    actual_real_Cramer_two_matrix_difference_cancel
      b1 w1 b2 w2 Z1 Z2 hdet1Ne hdet2
  have hCancel' :
      F + (d.1 : ℂ) * b1 + (d.2 : ℂ) * w1 = 0 := by
    simpa only [F, d, p1, p2] using hCancel
  have hInv :=
    actual_complex_columns_real_cancellation_bound
      a B ha hB b1 w1 F d hb1 hw1 hdet1 hCancel'
  have hMax : ‖d‖ ≤ |d.1| + |d.2| := by
    change max |d.1| |d.2| ≤ _
    exact max_le
      (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _))
  have hF :
      ‖F‖ ≤ ‖Z1-Z2‖ + |p2.1| * ‖b1-b2‖ +
          |p2.2| * ‖w1-w2‖ := by
    dsimp [F]
    calc
      _ ≤ (‖Z1-Z2‖ + ‖(p2.1 : ℂ) * (b1-b2)‖) +
          ‖(p2.2 : ℂ) * (w1-w2)‖ :=
        (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) (le_refl _))
      _ = _ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hCoef : 0 ≤ 1024 / (a * B ^ 2) := by positivity
  calc
    ‖p1-p2‖ = ‖d‖ := rfl
    _ ≤ |d.1| + |d.2| := hMax
    _ ≤ 1024 / (a * B ^ 2) * ‖F‖ := hInv
    _ ≤ (1024 / (a * B ^ 2)) *
        (‖Z1-Z2‖ + |p2.1| * ‖b1-b2‖ +
          |p2.2| * ‖w1-w2‖) :=
      mul_le_mul_of_nonneg_left hF hCoef

end HBL.TypeIIDynamicSelection
