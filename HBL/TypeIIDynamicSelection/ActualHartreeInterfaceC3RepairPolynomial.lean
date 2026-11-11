import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
Constructive finite-jet repair for the original Hartree interface gate.
Only the polynomial endpoint jets are certified here. No PDE residual
estimate, parameter Lipschitz estimate, or physical orbit is assumed or
claimed. For complex curvatures apply the real construction componentwise.
The physical three-interface nonlocal feedback remains to be estimated.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

namespace HBL.TypeIIDynamicSelection
open Polynomial

def hartreeInterfaceHermite2 : Polynomial ℝ :=
  C 2 * X ^ 7 - C (15 / 2) * X ^ 6 + C 10 * X ^ 5 -
    C 5 * X ^ 4 + C (1 / 2) * X ^ 2

def hartreeInterfaceHermite3 : Polynomial ℝ :=
  C (1 / 6) * X ^ 7 - C (2 / 3) * X ^ 6 + X ^ 5 -
    C (2 / 3) * X ^ 4 + C (1 / 6) * X ^ 3

def actualHartreePhysicalC3RepairPolynomial
    (L h d2 d3 : ℝ) : Polynomial ℝ :=
  (C (d2 * h ^ 2) * hartreeInterfaceHermite2 +
    C (d3 * h ^ 3) * hartreeInterfaceHermite3).comp
      (C h⁻¹ * (X - C L))

/-- All physical endpoint jets, with the true interval width. The left
value and slope stay zero, while the prescribed second and third jets are
produced, not postulated. All four right jets vanish exactly. -/
theorem actual_Hartree_physical_C3_repair_endpoint_jets
    (L h d2 d3 : ℝ) (hh : 0 < h) :
    let P := actualHartreePhysicalC3RepairPolynomial L h d2 d3
    P.eval L = 0 ∧
    P.derivative.eval L = 0 ∧
    P.derivative.derivative.eval L = d2 ∧
    P.derivative.derivative.derivative.eval L = d3 ∧
    P.eval (L + h) = 0 ∧
    P.derivative.eval (L + h) = 0 ∧
    P.derivative.derivative.eval (L + h) = 0 ∧
    P.derivative.derivative.derivative.eval (L + h) = 0 := by
  dsimp only
  repeat' apply And.intro
  all_goals
    norm_num [actualHartreePhysicalC3RepairPolynomial,
      hartreeInterfaceHermite2, hartreeInterfaceHermite3,
      Polynomial.derivative_comp, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_pow]
  all_goals field_simp [hh.ne']
  all_goals ring

/-- The two dimensionless kernels agree with their factored, localized
Hermite forms. This certificate is polynomial algebra only. -/
theorem actual_Hartree_C3_repair_factored_kernels :
    hartreeInterfaceHermite2 = C (1 / 2) * X ^ 2 * (1 - X) ^ 4 * (1 + C 4 * X) ∧
    hartreeInterfaceHermite3 = C (1 / 6) * X ^ 3 * (1 - X) ^ 4 := by
  constructor
  · apply Polynomial.funext
    intro x
    simp only [hartreeInterfaceHermite2, eval_add, eval_sub, eval_mul,
      eval_pow, eval_C, eval_X, eval_one]
    ring
  · apply Polynomial.funext
    intro x
    simp only [hartreeInterfaceHermite3, eval_add, eval_sub, eval_mul,
      eval_pow, eval_C, eval_X, eval_one]
    ring

end HBL.TypeIIDynamicSelection
