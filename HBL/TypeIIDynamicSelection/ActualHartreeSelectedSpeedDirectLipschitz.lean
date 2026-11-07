import HBL.TypeIIDynamicSelection.ActualHartreeCramerSelector
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCoupledInverseBound
import Mathlib.Tactic

/-!
# Direct Lipschitz control of the genuine real two-channel Cramer selector

The two full compatibility columns are fixed by the same moment-locked
Fredholm/Kummer construction. The Cramer selection is exactly linear in
the original complex obstruction Z, with no derivative of the source.

The quantitative bound uses the ACTUAL determinant and column budgets.
This establishes the finite-dimensional speed-selection Lipschitz interface;
the separate proof that an evolving full Hartree PDE obstruction has
the required s^(-9/4) difference remains a physical source obligation.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

theorem actual_real_Cramer_source_difference_exact
    (b w Z1 Z2 : ℂ) :
    actualRealCramerCorrection b w Z1 -
      actualRealCramerCorrection b w Z2 =
    actualRealCramerCorrection b w (Z1 - Z2) := by
  let d : ℝ := b.re * w.im - w.re * b.im
  apply Prod.ext
  · change
      (w.re * Z1.im - w.im * Z1.re) / d -
        (w.re * Z2.im - w.im * Z2.re) / d =
      (w.re * (Z1 - Z2).im - w.im * (Z1 - Z2).re) / d
    rw [Complex.sub_re, Complex.sub_im]
    ring
  · change
      (b.im * Z1.re - b.re * Z1.im) / d -
        (b.im * Z2.re - b.re * Z2.im) / d =
      (b.im * (Z1 - Z2).re - b.re * (Z1 - Z2).im) / d
    rw [Complex.sub_re, Complex.sub_im]
    ring

/-- Direct source-to-speed Lipschitz estimate, with the true normalized
two-column determinant. No formal derivative with respect to data is used. -/
theorem actual_real_Cramer_source_difference_bound
    (a B : ℝ) (ha : 0 < a) (hB : 0 < B)
    (b w Z1 Z2 : ℂ)
    (hb : ‖b‖ ≤ a * B ^ 2)
    (hw : ‖w‖ ≤ a * B ^ 2)
    (hdet : a ^ 2 * B ^ 4 / 256 ≤
      b.re * w.im - w.re * b.im) :
    ‖actualRealCramerCorrection b w Z1 -
      actualRealCramerCorrection b w Z2‖ ≤
      (1024 / (a * B ^ 2)) * ‖Z1 - Z2‖ := by
  have hdetPos :
      0 < b.re * w.im - w.re * b.im :=
    (by positivity : 0 < a ^ 2 * B ^ 4 / 256).trans_le hdet
  have hcancel :=
    actual_real_Cramer_correction_cancel b w (Z1 - Z2) hdetPos.ne'
  have hraw :=
    actual_complex_columns_real_cancellation_bound
      a B ha hB b w (Z1 - Z2)
      (actualRealCramerCorrection b w (Z1 - Z2))
      hb hw hdet hcancel
  have hExact :=
    actual_real_Cramer_source_difference_exact b w Z1 Z2
  rw [← hExact] at hraw
  have hplus :
      |(actualRealCramerCorrection b w Z1 -
        actualRealCramerCorrection b w Z2).1| ≤
        1024 / (a * B ^ 2) * ‖Z1 - Z2‖ :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans hraw
  have hminus :
      |(actualRealCramerCorrection b w Z1 -
        actualRealCramerCorrection b w Z2).2| ≤
        1024 / (a * B ^ 2) * ‖Z1 - Z2‖ :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans hraw
  change max
      |(actualRealCramerCorrection b w Z1 -
        actualRealCramerCorrection b w Z2).1|
      |(actualRealCramerCorrection b w Z1 -
        actualRealCramerCorrection b w Z2).2| ≤ _
  exact max_le hplus hminus

/-- Fixed-time weighted direct Lipschitz bound for a physical obstruction.
The only remaining hypothesis is the separately visible physical source
difference estimate; no rate, C1 field or tangent is hidden in a definition. -/
theorem actual_real_Cramer_order_lipschitz_from_source
    (a B s nu L : ℝ)
    (ha : 0 < a) (hB : 0 < B) (hs : 1 ≤ s)
    (hL : 0 ≤ L)
    (b w : ℂ)
    (hb : ‖b‖ ≤ a * B ^ 2)
    (hw : ‖w‖ ≤ a * B ^ 2)
    (hdet : a ^ 2 * B ^ 4 / 256 ≤
      b.re * w.im - w.re * b.im)
    (Z : ℝ × ℝ → ℂ)
    (hZ : ∀ theta eta : ℝ × ℝ,
      ‖Z theta - Z eta‖ ≤
        L * s ^ (-nu) * ‖theta - eta‖)
    (theta eta : ℝ × ℝ) :
    ‖actualRealCramerCorrection b w (Z theta) -
        actualRealCramerCorrection b w (Z eta)‖ ≤
      (1024 / (a * B ^ 2) * L) *
        s ^ (-nu) * ‖theta - eta‖ := by
  have hSpeed :=
    actual_real_Cramer_source_difference_bound
      a B ha hB b w (Z theta) (Z eta) hb hw hdet
  have hSrc := hZ theta eta
  have hFactor : 0 ≤ 1024 / (a * B ^ 2) := by positivity
  calc
    _ ≤ (1024 / (a * B ^ 2)) * ‖Z theta - Z eta‖ := hSpeed
    _ ≤ (1024 / (a * B ^ 2)) *
          (L * s ^ (-nu) * ‖theta - eta‖) :=
      mul_le_mul_of_nonneg_left hSrc hFactor
    _ = (1024 / (a * B ^ 2) * L) *
          s ^ (-nu) * ‖theta - eta‖ := by ring

end HBL.TypeIIDynamicSelection
