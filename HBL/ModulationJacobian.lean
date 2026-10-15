import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
First proof target: prop:modulation (local dynamic modulation).
This module checks its pointwise symmetry derivatives and normalized tangent
coordinate map. It does NOT claim the full local modulation theorem.
Pending: the radial homogeneous Sobolev realization, continuity of the test
functionals, joint C1 regularity after testing, and the parameterized implicit
function theorem with local uniqueness. No later proof target is accepted here.
-/

noncomputable section
namespace HBL.Modulation

/-- The radial bubble, defined on all real radii. -/
def bubble (r : ℝ) : ℝ := (Real.sqrt (1 + r ^ 2))⁻¹

/-- Radial scaling generator. -/
def dilationGenerator (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  f r / 2 + r * deriv f r

/-- Pullback by logarithmic scale. -/
def scalePullback (f : ℝ → ℝ) (a r : ℝ) : ℝ :=
  Real.exp (-a / 2) * f (Real.exp (-a) * r)

/-- Real and imaginary components of the phase pullback of a real profile. -/
def phasePullback (f : ℝ → ℝ) (g r : ℝ) : ℝ × ℝ :=
  (Real.cos g * f r, -Real.sin g * f r)

theorem bubble_differentiable (r : ℝ) : DifferentiableAt ℝ bubble r := by
  have h : DifferentiableAt ℝ (fun x : ℝ => 1 + x ^ 2) r := by fun_prop
  have hp : 0 < 1 + r ^ 2 := by positivity
  exact (h.sqrt (ne_of_gt hp)).inv (ne_of_gt (Real.sqrt_pos.2 hp))

/-- Chain rule for the first symmetry derivative, at each fixed radius. -/
theorem scalePullback_hasDerivAt {f : ℝ → ℝ} {r d : ℝ}
    (hf : HasDerivAt f d r) :
    HasDerivAt (fun a => scalePullback f a r) (-(f r / 2 + r * d)) 0 := by
  have h₁ : HasDerivAt (fun a : ℝ => Real.exp (-a / 2)) (-(1 / 2 : ℝ)) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).neg).div_const 2).exp using 1 <;> norm_num
  have h₂ : HasDerivAt (fun a : ℝ => Real.exp (-a) * r) (-r) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).neg.exp).mul_const r using 1 <;> simp
  have hfr : HasDerivAt f d (Real.exp (-(0 : ℝ)) * r) := by simpa using hf
  have h₃ : HasDerivAt (fun a : ℝ => f (Real.exp (-a) * r)) (d * (-r)) 0 :=
    hfr.comp 0 h₂
  convert h₁.mul h₃ using 1 <;>
    simp only [scalePullback, neg_zero, zero_div, Real.exp_zero, one_mul] <;>
    (try funext a) <;> ring

theorem bubble_scale_derivative (r : ℝ) :
    HasDerivAt (fun a => scalePullback bubble a r)
      (-dilationGenerator bubble r) 0 := by
  exact scalePullback_hasDerivAt (bubble_differentiable r).hasDerivAt

/-- The second symmetry derivative, in real coordinates, at each fixed radius. -/
theorem phasePullback_hasDerivAt (f : ℝ → ℝ) (r : ℝ) :
    HasDerivAt (fun g => phasePullback f g r) (0, -f r) 0 := by
  have h₁ : HasDerivAt (fun g : ℝ => Real.cos g * f r) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).mul_const (f r)
  have h₂ : HasDerivAt (fun g : ℝ => -Real.sin g * f r) (-f r) 0 := by
    simpa using (Real.hasDerivAt_sin 0).neg.mul_const (f r)
  exact h₁.prodMk h₂

section TangentCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Coordinates of the two symmetry tangent directions under real test maps. -/
def tangentCoordinates (ellPlus ellMinus : E →L[ℝ] ℝ) (w z : E)
    (p : ℝ × ℝ) : ℝ × ℝ :=
  (ellPlus ((-p.1) • z), ellMinus ((-p.2) • w))

/-- Normalization gives the negative identity, with both cross terms absent. -/
theorem tangentCoordinates_eq_neg (ellPlus ellMinus : E →L[ℝ] ℝ) (w z : E)
    (hPlus : ellPlus z = 1) (hMinus : ellMinus w = 1) (p : ℝ × ℝ) :
    tangentCoordinates ellPlus ellMinus w z p = -p := by
  ext <;> simp [tangentCoordinates, hPlus, hMinus]

/-- Invertibility of the normalized two-parameter tangent coordinate map. -/
theorem tangentCoordinates_bijective (ellPlus ellMinus : E →L[ℝ] ℝ) (w z : E)
    (hPlus : ellPlus z = 1) (hMinus : ellMinus w = 1) :
    Function.Bijective (tangentCoordinates ellPlus ellMinus w z) := by
  have h : tangentCoordinates ellPlus ellMinus w z = fun p => -p := by
    funext p
    exact tangentCoordinates_eq_neg ellPlus ellMinus w z hPlus hMinus p
  rw [h]
  exact ⟨neg_injective, fun p => ⟨-p, neg_neg p⟩⟩

end TangentCoordinates
end HBL.Modulation
