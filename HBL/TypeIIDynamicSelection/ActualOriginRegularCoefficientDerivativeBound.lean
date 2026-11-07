import HBL.TypeIIDynamicSelection.ActualOriginRegularCoefficientTimeDerivative
import Mathlib.Tactic

/-!
# Quantitative time bound for the moving regular Kummer coefficient

The exact derivative has already been derived from the moving lower Cauchy
jet. Here the origin-basis bounds and the exact Wronskian inverse are used to
give a norm estimate with no artificial inverse power of the small lower
endpoint.

This is the quantitative producer needed before inserting the actual Fredholm
jet time bounds.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_origin_regular_coeff_moving_dot_norm_le
    {mu theta scale lo hi C D : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K lo hi C)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (r0 : ℝ → ℝ) (U DU : ℝ → ℂ)
    (s r0dot : ℝ) (Udot DUdot : ℂ)
    (hr : r0 s ∈ Ioo lo hi)
    (hcoeff :
      ‖frozenFirstCoeff (r0 s)‖ + ‖frozenZeroCoeff mu theta‖ ≤ D) :
    ‖actualOriginRegularCoeffFromMovingJetDot
        K r0 U DU s r0dot Udot DUdot‖ ≤
      C ^ 2 *
        (‖Udot‖ + ‖DUdot‖ +
          |r0dot| * (1 + 3 * D) * (‖U s‖ + ‖DU s‖)) := by
  let r : ℝ := r0 s
  let Y : ℂ := originPhysicalValue K.y r
  let Yp : ℂ := originPhysicalSlope K.y K.dy r
  let A : ℂ := frozenFirstCoeff r
  let B0 : ℂ := frozenZeroCoeff mu theta
  let Ypp : ℂ := -(A * Yp + B0 * Y)
  let W : ℂ := originGreenWronskian K r
  let N : ℂ := Y * DU s - Yp * U s
  let Ndot : ℂ :=
    (r0dot • Yp) * DU s + Y * DUdot -
      ((r0dot • Ypp) * U s + Yp * Udot)
  have hrcc : r ∈ Icc lo hi := ⟨hr.1.le, hr.2.le⟩
  obtain ⟨_hYd,_hYpd,_hXd,_hXpd,_hWexact,hWne,
    hY,hYp,_hX,_hXp,hWinv⟩ := hK r hrcc
  have hA : ‖A‖ ≤ D := by
    dsimp [A, r]
    exact (le_add_of_nonneg_right (norm_nonneg (frozenZeroCoeff mu theta))).trans
      hcoeff
  have hB0 : ‖B0‖ ≤ D := by
    dsimp [B0, r]
    exact (le_add_of_nonneg_left (norm_nonneg (frozenFirstCoeff (r0 s)))).trans
      hcoeff
  have hYppSafe : ‖Ypp‖ ≤ 2 * D * C := by
    calc
      _ ≤ ‖A * Yp‖ + ‖B0 * Y‖ := by
        dsimp [Ypp]
        rw [norm_neg]
        exact norm_add_le _ _
      _ = ‖A‖ * ‖Yp‖ + ‖B0‖ * ‖Y‖ := by rw [norm_mul, norm_mul]
      _ ≤ D * C + D * C :=
        add_le_add
          (mul_le_mul hA hYp (norm_nonneg _) hD)
          (mul_le_mul hB0 hY (norm_nonneg _) hD)
      _ = 2 * D * C := by ring
  have hN :
      ‖N‖ ≤ C * (‖DU s‖ + ‖U s‖) := by
    dsimp [N]
    calc
      _ ≤ ‖Y * DU s‖ + ‖Yp * U s‖ := norm_sub_le _ _
      _ = ‖Y‖ * ‖DU s‖ + ‖Yp‖ * ‖U s‖ := by rw [norm_mul, norm_mul]
      _ ≤ C * ‖DU s‖ + C * ‖U s‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_right hY (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hYp (norm_nonneg _))
      _ = C * (‖DU s‖ + ‖U s‖) := by ring
  have hNdot :
      ‖Ndot‖ ≤ C *
        (‖Udot‖ + ‖DUdot‖ +
          |r0dot| * (‖DU s‖ + 2 * D * ‖U s‖)) := by
    have hsmulYp : ‖r0dot • Yp‖ ≤ |r0dot| * C := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hYp (abs_nonneg r0dot)
    have hsmulYpp : ‖r0dot • Ypp‖ ≤ |r0dot| * (2 * D * C) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hYppSafe (abs_nonneg r0dot)
    dsimp [Ndot]
    calc
      _ ≤ ‖(r0dot • Yp) * DU s + Y * DUdot‖ +
          ‖(r0dot • Ypp) * U s + Yp * Udot‖ := norm_sub_le _ _
      _ ≤ (‖(r0dot • Yp) * DU s‖ + ‖Y * DUdot‖) +
          (‖(r0dot • Ypp) * U s‖ + ‖Yp * Udot‖) :=
        add_le_add (norm_add_le _ _) (norm_add_le _ _)
      _ = (‖r0dot • Yp‖ * ‖DU s‖ + ‖Y‖ * ‖DUdot‖) +
          (‖r0dot • Ypp‖ * ‖U s‖ + ‖Yp‖ * ‖Udot‖) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
      _ ≤ ((|r0dot| * C) * ‖DU s‖ + C * ‖DUdot‖) +
          ((|r0dot| * (2 * D * C)) * ‖U s‖ + C * ‖Udot‖) :=
        add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hsmulYp (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hY (norm_nonneg _)))
          (add_le_add
            (mul_le_mul_of_nonneg_right hsmulYpp (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hYp (norm_nonneg _)))
      _ = C * (‖Udot‖ + ‖DUdot‖ +
          |r0dot| * (‖DU s‖ + 2 * D * ‖U s‖)) := by ring
  have hAterm :
      ‖N * ((r0dot : ℂ) * A)‖ ≤
        C * (‖DU s‖ + ‖U s‖) * (|r0dot| * D) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul
      hN
      (mul_le_mul_of_nonneg_left hA (abs_nonneg r0dot))
      (mul_nonneg (abs_nonneg r0dot) (norm_nonneg A))
      (mul_nonneg hC (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hWrewrite :
      actualOriginRegularCoeffFromMovingJetDot
          K r0 U DU s r0dot Udot DUdot =
        (Ndot + N * ((r0dot : ℂ) * A)) * W⁻¹ := by
    dsimp [actualOriginRegularCoeffFromMovingJetDot, Ndot, N, W, Ypp,
      Y, Yp, A, B0, r]
    field_simp [hWne]
    ring
  rw [hWrewrite, norm_mul]
  have hSum :
      ‖Ndot + N * ((r0dot : ℂ) * A)‖ ≤
        C * (‖Udot‖ + ‖DUdot‖ +
          |r0dot| * (1 + 3 * D) * (‖U s‖ + ‖DU s‖)) := by
    calc
      _ ≤ ‖Ndot‖ + ‖N * ((r0dot : ℂ) * A)‖ := norm_add_le _ _
      _ ≤ C * (‖Udot‖ + ‖DUdot‖ +
            |r0dot| * (‖DU s‖ + 2 * D * ‖U s‖)) +
          C * (‖DU s‖ + ‖U s‖) * (|r0dot| * D) :=
        add_le_add hNdot hAterm
      _ ≤ C * (‖Udot‖ + ‖DUdot‖ +
          |r0dot| * (1 + 3 * D) * (‖U s‖ + ‖DU s‖)) := by
        have hnonU : 0 ≤ ‖U s‖ := norm_nonneg _
        have hnonDU : 0 ≤ ‖DU s‖ := norm_nonneg _
        have habs : 0 ≤ |r0dot| := abs_nonneg _
        nlinarith [
          mul_nonneg hD hnonDU,
          mul_nonneg hD hnonU,
          mul_nonneg habs hnonU,
          mul_nonneg habs (mul_nonneg hD hnonDU)]
  calc
    ‖Ndot + N * ((r0dot : ℂ) * A)‖ * ‖W⁻¹‖
        ≤ (C * (‖Udot‖ + ‖DUdot‖ +
          |r0dot| * (1 + 3 * D) * (‖U s‖ + ‖DU s‖))) * C :=
      mul_le_mul hSum hWinv (norm_nonneg _) (by positivity)
    _ = C ^ 2 *
        (‖Udot‖ + ‖DUdot‖ +
          |r0dot| * (1 + 3 * D) * (‖U s‖ + ‖DU s‖)) := by ring

end HBL.TypeIIDynamicSelection
