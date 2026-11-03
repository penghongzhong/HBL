import Mathlib.Tactic

/-!
# HBL revised 2.13: three scale/radius envelopes for the real Hartree interaction

For 0 < ell <= 1 and r >= 0, put d=1+r and q=1+ell*r.
The two essential geometric inequalities are 1 <= q and ell*d <= q.
The genuine full nonlinear Hartree interaction, once the separately
audited core, pure, and mixed radial Riesz tails and complex-cubic
Lipschitz estimate are used, reduces to the following three envelopes.

This is a scalar bridge; neither the full physical source identification
nor three-region matching or the Type-II rate is claimed by this lemma.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

/-- Three exact scalar power inequalities for the physical radial
weight sigma=7/4 and the energy-critical Hartree scale. -/
theorem actual_Hartree_three_Fredholm_scalar_envelopes
    (ell r : ℝ) (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hr : 0 ≤ r) :
    ell ^ (1 / 2 : ℝ) * (1 + r) ^ (-(5 / 4 : ℝ)) /
        (1 + ell * r) ≤
      ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) ∧
    ell ^ (1 : ℝ) * (1 + r) ^ (-(1 / 4 : ℝ)) /
        (1 + ell * r) ^ 2 ≤
      ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) ∧
    ell ^ (3 / 2 : ℝ) * (1 + r) ^ (3 / 4 : ℝ) /
        (1 + ell * r) ^ 3 ≤
      ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) := by
  let d : ℝ := 1 + r
  let q : ℝ := 1 + ell * r
  have hd : 0 < d := by dsimp [d]; linarith
  have hdOne : 1 ≤ d := by dsimp [d]; linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hqOne : 1 ≤ q := by
    dsimp [q]
    nlinarith [mul_nonneg hell.le hr]
  have hScale : ell * d ≤ q := by
    dsimp [d,q]
    nlinarith [hellOne]
  have hTargetNonneg :
      0 ≤ ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ)) := by
    positivity
  constructor
  · have hEllSmall : ell ^ (3 / 8 : ℝ) ≤ 1 := by
      simpa only [Real.one_rpow] using
        (Real.rpow_le_rpow hell.le hellOne
          (show (0 : ℝ) ≤ (3 / 8 : ℝ) by norm_num))
    have hEllSplit :
        ell ^ (1 / 2 : ℝ) =
          ell ^ (1 / 8 : ℝ) * ell ^ (3 / 8 : ℝ) := by
      calc
        _ = ell ^ ((1 / 8 : ℝ) + (3 / 8 : ℝ)) := by norm_num
        _ = _ := Real.rpow_add hell _ _
    have hEll :
        ell ^ (1 / 2 : ℝ) ≤ ell ^ (1 / 8 : ℝ) := by
      calc
        _ = ell ^ (1 / 8 : ℝ) * ell ^ (3 / 8 : ℝ) := hEllSplit
        _ ≤ ell ^ (1 / 8 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hEllSmall (by positivity)
        _ = _ := by ring
    have hRad :
        d ^ (-(5 / 4 : ℝ)) ≤ d ^ (-(5 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hdOne (by norm_num)
    have hProd :
        ell ^ (1 / 2 : ℝ) * d ^ (-(5 / 4 : ℝ)) ≤
          ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ)) :=
      mul_le_mul hEll hRad (by positivity) (by positivity)
    change ell ^ (1 / 2 : ℝ) * d ^ (-(5 / 4 : ℝ)) / q ≤
      ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))
    apply (div_le_iff₀ hq).2
    calc
      ell ^ (1 / 2 : ℝ) * d ^ (-(5 / 4 : ℝ)) ≤
          ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ)) := hProd
      _ = (ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))) * 1 := by ring
      _ ≤ (ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))) * q :=
        mul_le_mul_of_nonneg_left hqOne hTargetNonneg
  constructor
  · have hDRpow :
        d ^ (3 / 8 : ℝ) ≤ d ^ (7 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hdOne (by norm_num)
    have hScaled :
        ell ^ (7 / 8 : ℝ) * d ^ (3 / 8 : ℝ) ≤ q ^ 2 := by
      calc
        ell ^ (7 / 8 : ℝ) * d ^ (3 / 8 : ℝ) ≤
            ell ^ (7 / 8 : ℝ) * d ^ (7 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_left hDRpow (by positivity)
        _ = (ell * d) ^ (7 / 8 : ℝ) :=
          (Real.mul_rpow hell.le hd.le).symm
        _ ≤ q ^ (7 / 8 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hScale (by norm_num)
        _ ≤ q ^ 2 := by
          have hStep := Real.rpow_le_rpow_of_exponent_le hqOne
            (show (7 / 8 : ℝ) ≤ 2 by norm_num)
          exact hStep.trans_eq (Real.rpow_natCast q 2)
    have hEllSplit :
        ell ^ (1 : ℝ) =
          ell ^ (1 / 8 : ℝ) * ell ^ (7 / 8 : ℝ) := by
      calc
        _ = ell ^ ((1 / 8 : ℝ) + (7 / 8 : ℝ)) := by norm_num
        _ = _ := Real.rpow_add hell _ _
    have hRadSplit :
        d ^ (-(1 / 4 : ℝ)) =
          d ^ (-(5 / 8 : ℝ)) * d ^ (3 / 8 : ℝ) := by
      calc
        _ = d ^ ((-(5 / 8 : ℝ)) + (3 / 8 : ℝ)) := by norm_num
        _ = _ := Real.rpow_add hd _ _
    change ell ^ (1 : ℝ) * d ^ (-(1 / 4 : ℝ)) / q ^ 2 ≤
      ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))
    apply (div_le_iff₀ (pow_pos hq 2)).2
    calc
      ell ^ (1 : ℝ) * d ^ (-(1 / 4 : ℝ)) =
          (ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))) *
            (ell ^ (7 / 8 : ℝ) * d ^ (3 / 8 : ℝ)) := by
        rw [hEllSplit, hRadSplit]
        ring
      _ ≤ (ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))) * q ^ 2 :=
        mul_le_mul_of_nonneg_left hScaled hTargetNonneg
  · have hScaled :
        ell ^ (11 / 8 : ℝ) * d ^ (11 / 8 : ℝ) ≤ q ^ 3 := by
      calc
        ell ^ (11 / 8 : ℝ) * d ^ (11 / 8 : ℝ) =
            (ell * d) ^ (11 / 8 : ℝ) :=
          (Real.mul_rpow hell.le hd.le).symm
        _ ≤ q ^ (11 / 8 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hScale (by norm_num)
        _ ≤ q ^ 3 := by
          have hStep := Real.rpow_le_rpow_of_exponent_le hqOne
            (show (11 / 8 : ℝ) ≤ 3 by norm_num)
          exact hStep.trans_eq (Real.rpow_natCast q 3)
    have hEllSplit :
        ell ^ (3 / 2 : ℝ) =
          ell ^ (1 / 8 : ℝ) * ell ^ (11 / 8 : ℝ) := by
      calc
        _ = ell ^ ((1 / 8 : ℝ) + (11 / 8 : ℝ)) := by norm_num
        _ = _ := Real.rpow_add hell _ _
    have hRadSplit :
        d ^ (3 / 4 : ℝ) =
          d ^ (-(5 / 8 : ℝ)) * d ^ (11 / 8 : ℝ) := by
      calc
        _ = d ^ ((-(5 / 8 : ℝ)) + (11 / 8 : ℝ)) := by norm_num
        _ = _ := Real.rpow_add hd _ _
    change ell ^ (3 / 2 : ℝ) * d ^ (3 / 4 : ℝ) / q ^ 3 ≤
      ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))
    apply (div_le_iff₀ (pow_pos hq 3)).2
    calc
      ell ^ (3 / 2 : ℝ) * d ^ (3 / 4 : ℝ) =
          (ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))) *
            (ell ^ (11 / 8 : ℝ) * d ^ (11 / 8 : ℝ)) := by
        rw [hEllSplit, hRadSplit]
        ring
      _ ≤ (ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))) * q ^ 3 :=
        mul_le_mul_of_nonneg_left hScaled hTargetNonneg

end HBL.TypeIIDynamicSelection
