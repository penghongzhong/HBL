import Mathlib.Tactic

/-!
# Complete original quartic Hartree Taylor: algebraic six-product fifth-weight control

The original nonlocal Taylor remainder is exactly the sum of the
six products P0*CR + P1*(C1+CR) + PR*(C0+C1+CR).
The slowest contribution is PR*C0 with only a half-radial cubic
background and true inverse-radius Riesz decay; the other five
products are faster. This is the exact scalar estimate needed
to combine the independently proved ORIGINAL Riesz potential rows.

No synthetic time order, independent source, PDE solvability, or
Type-II blowup law is supplied by this algebraic theorem.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

/-- The correct fifth power is exactly the square-integrable
L^(2,7/4) envelope. Actual physical Riesz and cubic producers
will instantiate all displayed coefficient budgets. -/
theorem actual_Hartree_six_original_nonlocal_Taylor_products_fifth_weight
    (t A0 A1 AR B1 BR K : ℝ)
    (ht : 1 ≤ t)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hAR : 0 ≤ AR)
    (hB1 : 0 ≤ B1) (hBR : 0 ≤ BR) (hK : 0 ≤ K)
    (P0 P1 PR C0 C1 CR : ℂ)
    (hp0 : t*‖P0‖ ≤ A0)
    (hp1 : t*‖P1‖ ≤ A1)
    (hpR : t*‖PR‖ ≤ AR)
    (hc0 : t^3*‖C0‖^2 ≤ K^3)
    (hc1 : t^2*‖C1‖ ≤ B1)
    (hcR : t^2*‖CR‖ ≤ BR) :
    t^5*‖P0*CR+P1*(C1+CR)+PR*(C0+C1+CR)‖^2 ≤
      2*(AR^2*K^3+((A0+A1+AR)*(B1+BR))^2) := by
  let F : ℂ := PR*C0
  let G : ℂ := P0*CR+(P1+PR)*(C1+CR)
  let S : ℝ := (A0+A1+AR)*(B1+BR)
  have ht0 : 0 ≤ t := by linarith
  have hS0 : 0 ≤ S := by
    dsimp [S]
    positivity
  have hDecomp :
      P0*CR+P1*(C1+CR)+PR*(C0+C1+CR) = F+G := by
    dsimp [F,G]
    ring
  have hpSum :
      t*(‖P0‖+‖P1‖+‖PR‖) ≤ A0+A1+AR := by
    nlinarith [hp0,hp1,hpR]
  have hcSum :
      t^2*(‖C1‖+‖CR‖) ≤ B1+BR := by
    nlinarith [hc1,hcR]
  have hGnorm :
      ‖G‖ ≤
        (‖P0‖+‖P1‖+‖PR‖)*(‖C1‖+‖CR‖) := by
    dsimp [G]
    have hPM := norm_add_le P1 PR
    have hCM := norm_add_le C1 CR
    have hPMul :
        ‖P1+PR‖*‖C1+CR‖ ≤
          (‖P1‖+‖PR‖)*(‖C1‖+‖CR‖) :=
      mul_le_mul hPM hCM (norm_nonneg _) (by positivity)
    calc
      _ ≤ ‖P0*CR‖+‖(P1+PR)*(C1+CR)‖ :=
        norm_add_le _ _
      _ = ‖P0‖*‖CR‖+‖P1+PR‖*‖C1+CR‖ := by
        simp only [norm_mul]
      _ ≤ ‖P0‖*‖CR‖+
          (‖P1‖+‖PR‖)*(‖C1‖+‖CR‖) :=
        add_le_add_left hPMul _
      _ ≤ (‖P0‖+‖P1‖+‖PR‖)*(‖C1‖+‖CR‖) := by
        nlinarith [mul_nonneg (norm_nonneg P0) (norm_nonneg C1)]
  have hGnormTime :
      t^3*‖G‖ ≤ S := by
    calc
      _ ≤ t^3*
          ((‖P0‖+‖P1‖+‖PR‖)*(‖C1‖+‖CR‖)) :=
        mul_le_mul_of_nonneg_left hGnorm (pow_nonneg ht0 _)
      _ = (t*(‖P0‖+‖P1‖+‖PR‖))*
          (t^2*(‖C1‖+‖CR‖)) := by ring
      _ ≤ (A0+A1+AR)*(B1+BR) :=
        mul_le_mul hpSum hcSum (by positivity) (by positivity)
      _ = S := rfl
  have hPRSq :
      (t*‖PR‖)^2 ≤ AR^2 :=
    pow_le_pow_left₀ (mul_nonneg ht0 (norm_nonneg _)) hpR 2
  have hFTime :
      t^5*‖F‖^2 ≤ AR^2*K^3 := by
    calc
      _ = (t*‖PR‖)^2*(t^3*‖C0‖^2) := by
        dsimp [F]
        rw [norm_mul]
        ring
      _ ≤ AR^2*K^3 :=
        mul_le_mul hPRSq hc0 (by positivity) (sq_nonneg _)
  have ht5 : t^5 ≤ t^6 := by
    have h := mul_le_mul_of_nonneg_left ht (pow_nonneg ht0 5)
    nlinarith [h]
  have hGSq :
      t^5*‖G‖^2 ≤ S^2 := by
    have hSq : (t^3*‖G‖)^2 ≤ S^2 :=
      pow_le_pow_left₀ (mul_nonneg (pow_nonneg ht0 3) (norm_nonneg _))
        hGnormTime 2
    calc
      _ ≤ t^6*‖G‖^2 :=
        mul_le_mul_of_nonneg_right ht5 (sq_nonneg _)
      _ = (t^3*‖G‖)^2 := by ring
      _ ≤ S^2 := hSq
  have hNormSum :
      ‖F+G‖^2 ≤ (‖F‖+‖G‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le F G) 2
  have hSqSum :
      (‖F‖+‖G‖)^2 ≤ 2*(‖F‖^2+‖G‖^2) := by
    nlinarith [sq_nonneg (‖F‖-‖G‖)]
  rw [hDecomp]
  calc
    t^5*‖F+G‖^2 ≤ t^5*(‖F‖+‖G‖)^2 :=
      mul_le_mul_of_nonneg_left hNormSum (pow_nonneg ht0 5)
    _ ≤ t^5*(2*(‖F‖^2+‖G‖^2)) :=
      mul_le_mul_of_nonneg_left hSqSum (pow_nonneg ht0 5)
    _ = 2*(t^5*‖F‖^2+t^5*‖G‖^2) := by ring
    _ ≤ 2*(AR^2*K^3+S^2) :=
      mul_le_mul_of_nonneg_left (add_le_add hFTime hGSq)
        (by norm_num)
    _ = 2*(AR^2*K^3+((A0+A1+AR)*(B1+BR))^2) := rfl

end HBL.TypeIIDynamicSelection
