import HBL.TypeIIDynamicSelection.ActualRadialSpatialFlatness
import Mathlib.Tactic

/-!
# Radial symmetry removes the centre-derivative input in physical flatness

The genuinely smooth radial cross section of any 3D regular Hartree
solution is an even complex function of the signed radial coordinate.
Its spatial derivative at the origin is therefore ZERO, as derived
here using the actual chain rule and differentiability, not assumed.

When combined with the twice-applied real-to-complex mean value theorem
already in ActualRadialSpatialFlatness, the explicit rescaled
off-terminal bound has *no separate first-derivative-zero input*.

Remaining obligation: obtain the everywhere-even C² radial
representative and uniform Hessian bound from the same high Sobolev
regular Hartree flow. A merely almost-everywhere radial Lp field is
not directly usable pointwise at the origin.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection

theorem actual_even_complex_radial_deriv_zero
    (f : ℝ → ℂ)
    (hf : DifferentiableAt ℝ f 0)
    (heven : ∀ r : ℝ, f (-r) = f r) :
    deriv f 0 = 0 := by
  have hNegArg :
      HasDerivAt (fun r : ℝ => -r) (-1) (0 : ℝ) := by
    simpa using ((hasDerivAt_id (0 : ℝ)).neg)
  have hNeg :
      HasDerivAt (fun r : ℝ => f (-r)) (-(deriv f 0)) 0 := by
    simpa only [neg_one_smul] using
      (hf.hasDerivAt.comp (0 : ℝ) hNegArg)
  have heq : (fun r : ℝ => f (-r)) = f := by
    funext r
    exact heven r
  have hd : deriv f 0 = -(deriv f 0) := by
    have hh := hNeg.deriv
    rw [heq] at hh
    exact hh
  have hdouble : (2 : ℂ) * deriv f 0 = 0 := by
    calc
      _ = deriv f 0 - (-(deriv f 0)) := by ring
      _ = 0 := by rw [← hd]; ring
  exact (mul_eq_zero.mp hdouble).resolve_left (by norm_num)

/-- For the actual radial flow at any admissible time, evenness
and regularity REMOVE the artificial input z_r(t,0)=0 from the
critical-rescaling quadratic spatial flatness bound. -/
theorem actual_even_Hartree_offterminal_rescaled_flat_part
    (z : ℝ → ℝ → ℂ) (t ell r M : ℝ)
    (hell : 0 < ell) (hM : 0 ≤ M)
    (heven : ∀ x : ℝ, z t (-x) = z t x)
    (hDiff : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (z t) x)
    (hDiffSecond : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv (z t)) x)
    (hSecond : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖deriv (deriv (z t)) x‖ ≤ M)
    (hr : 0 ≤ r) (hcore : ell * r ≤ 1) :
    ‖rescalePhysicalRadiation ell (z t) r -
        (Real.sqrt ell : ℂ) * z t 0‖ ≤
      M * ell ^ 2 * Real.sqrt ell * r ^ 2 := by
  have hD0 : DifferentiableAt ℝ (z t) 0 :=
    hDiff 0 (by simp : (0 : ℝ) ∈ Icc 0 1)
  have hFirst : deriv (z t) 0 = 0 :=
    actual_even_complex_radial_deriv_zero (z t) hD0 heven
  exact actual_Hartree_offterminal_rescaled_flat_part
    z t ell r M hell hM hFirst hDiff hDiffSecond hSecond hr hcore

end HBL.TypeIIDynamicSelection
