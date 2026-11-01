import HBL.TypeIIDynamicSelection.ActualRadialOriginEven
import Mathlib.Tactic

/-!
# Physical Hartree trapped-window spatial source gain

The original manuscript only needs a uniform C² radial regular-flow
bound and its actual scale-trapping window, not an infinite hierarchy
of terminal time jets.

This file feeds the preceding genuine off-terminal radial Taylor
estimate into the ACTUAL physical length ell(s), the original
trapping upper bound ell(s)<=A*s^(-beta), and the moving bubble-core
radius R<=s^rho. All exponent conditions are derived algebraically
from beta>1/2; no limiting Type II exponent is imposed.

The C² representative and uniform high-regularity bound still need
to be instantiated from the external classical Hartree local theory;
no source flatness is assumed.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection

def actualOffterminalFlatGainExponent (beta rho : ℝ) : ℝ :=
  5 * beta / 2 - 2 * rho - 1

/-- The precise manuscript flatness threshold has a derived positive
margin, rather than treating epsilon_flat>0 as a supplied datum. -/
theorem actual_offterminal_flat_gain_margin_pos
    (beta rho : ℝ)
    (hbeta : (1 / 2 : ℝ) < beta)
    (hrho : 0 ≤ rho)
    (hupper : rho < (5 * beta - 2) / 4) :
    0 < actualOffterminalFlatGainExponent beta rho := by
  dsimp [actualOffterminalFlatGainExponent]
  linarith

/-- Every genuine trap exponent 1/2<beta<1 admits explicit moving-core
and flat-source gain exponents, with no prescribed final rate.
The choice ensures 0<rho<1/2 and epsilon_flat>0. -/
theorem actual_offterminal_choose_positive_flat_gain
    (beta : ℝ) (hb : (1 / 2 : ℝ) < beta) (hb1 : beta < 1) :
    ∃ rho epsilon : ℝ,
      0 < rho ∧ rho < 1 / 2 ∧ 0 < epsilon ∧
      -(5 * beta / 2) + 2 * rho = -1 - epsilon := by
  refine ⟨(5 * beta - 2) / 8, (5 * beta - 2) / 4,
    by linarith, by linarith, by linarith, by ring⟩

/-- FULL real nonterminal regular radiation, not a compactly supported
surrogate: a proven quadratic spatial flat source gain on the
actual moving trapped bubble core. The only analytic hypotheses are
uniform ordinary spatial C² bounds and radial evenness, which are
the proper Sobolev-flow realization interface.

No particular scale trajectory or terminal exponent is prescribed.
-/
theorem actual_Hartree_trapped_offterminal_flat_source
    (z : ℝ → ℝ → ℂ) (t s ell R M A beta rho : ℝ)
    (hell : 0 < ell) (hM : 0 ≤ M)
    (hs : 0 < s)
    (hTrap : ell ≤ A * s ^ (-beta))
    (hEven : ∀ x : ℝ, z t (-x) = z t x)
    (hDiff : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (z t) x)
    (hDiffSecond : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv (z t)) x)
    (hSecond : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖deriv (deriv (z t)) x‖ ≤ M)
    (hR : 0 ≤ R) (hRbound : R ≤ s ^ rho)
    (hCore : ell * R ≤ 1) :
    ‖rescalePhysicalRadiation ell (z t) R -
        (Real.sqrt ell : ℂ) * z t 0‖ ≤
      M * (A * s ^ (-beta)) ^ 2 *
        Real.sqrt (A * s ^ (-beta)) * (s ^ rho) ^ 2 := by
  let U : ℝ := A * s ^ (-beta)
  have hU : 0 < U := hell.trans_le hTrap
  have hEllSquare : ell ^ 2 ≤ U ^ 2 :=
    pow_le_pow_left₀ hell.le hTrap 2
  have hSqrt : Real.sqrt ell ≤ Real.sqrt U :=
    Real.sqrt_le_sqrt hTrap
  have hCoeff : ell ^ 2 * Real.sqrt ell ≤
      U ^ 2 * Real.sqrt U := by
    calc
      _ ≤ U ^ 2 * Real.sqrt ell :=
        mul_le_mul_of_nonneg_right hEllSquare (Real.sqrt_nonneg ell)
      _ ≤ U ^ 2 * Real.sqrt U :=
        mul_le_mul_of_nonneg_left hSqrt (sq_nonneg U)
  have hRPow : R ^ 2 ≤ (s ^ rho) ^ 2 :=
    pow_le_pow_left₀ hR hRbound 2
  have hMCoeff : 0 ≤ M * (U ^ 2 * Real.sqrt U) :=
    mul_nonneg hM (mul_nonneg (sq_nonneg U) (Real.sqrt_nonneg U))
  have hFlat := actual_even_Hartree_offterminal_rescaled_flat_part
    z t ell R M hell hM hEven hDiff hDiffSecond hSecond hR hCore
  calc
    _ ≤ M * ell ^ 2 * Real.sqrt ell * R ^ 2 := hFlat
    _ = M * (ell ^ 2 * Real.sqrt ell) * R ^ 2 := by ring
    _ ≤ M * (U ^ 2 * Real.sqrt U) * R ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCoeff hM) (sq_nonneg R)
    _ ≤ M * (U ^ 2 * Real.sqrt U) * (s ^ rho) ^ 2 :=
      mul_le_mul_of_nonneg_left hRPow hMCoeff
    _ = M * (A * s ^ (-beta)) ^ 2 *
        Real.sqrt (A * s ^ (-beta)) * (s ^ rho) ^ 2 := by
      dsimp [U]

end HBL.TypeIIDynamicSelection
