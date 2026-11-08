import HBL.TypeIIDynamicSelection.ActualWholeRadiationSelfCubic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Genuine local cubic multiplier in the original NONLOCAL 3D Hartree PDE

For u(t,r) complex, the actual Hartree multiplier is
  C(u)=|u|^2*u,
and not a substitute for the nonlocal Hartree term I[|u|^4]*C(u).
Its exact time derivative is
  C'(u) = 2*Re(conj(u)*u_t)*u + |u|^2*u_t.

The time derivative is derived from the same COMPLEX physical field,
including both real/imaginary channels and the u=0 case.
It is not postulated as a new source and has no prescribed rate.

This is the remaining local multiplier calculation for composing the
time derivatives of the genuine core, radiation and mixed logarithmic
Riesz potentials in the original four-piece Hartree source.
-/

noncomputable section
set_option autoImplicit false
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The genuine original |u|²u Hartree cubic time tangent. -/
def actualHartreeLocalCubicTimeVelocity (u du : ℂ) : ℂ :=
  ((2 * (u.re * du.re + u.im * du.im) : ℝ) : ℂ) * u +
    ((‖u‖ ^ 2 : ℝ) : ℂ) * du

private theorem hartree_complex_curve_re_hasDerivAt
    (u : ℝ → ℂ) (du : ℂ) (s : ℝ)
    (hu : HasDerivAt u du s) :
    HasDerivAt (fun t => (u t).re) du.re s := by
  have hc : HasDerivAt (fun _ : ℝ => Complex.reCLM)
      (0 : ℂ →L[ℝ] ℝ) s := hasDerivAt_const s Complex.reCLM
  have h := hc.clm_apply hu
  simpa only [zero_apply, zero_add, Complex.reCLM_apply] using h

private theorem hartree_complex_curve_im_hasDerivAt
    (u : ℝ → ℂ) (du : ℂ) (s : ℝ)
    (hu : HasDerivAt u du s) :
    HasDerivAt (fun t => (u t).im) du.im s := by
  have hc : HasDerivAt (fun _ : ℝ => Complex.imCLM)
      (0 : ℂ →L[ℝ] ℝ) s := hasDerivAt_const s Complex.imCLM
  have h := hc.clm_apply hu
  simpa only [zero_apply, zero_add, Complex.imCLM_apply] using h

/-- True time derivative of the local cubic physical multiplier from
one complex source time derivative; it is not an independent premise. -/
theorem actual_Hartree_local_cubic_multiplier_time_derivative
    (u : ℝ → ℝ → ℂ) (s r : ℝ) (du : ℂ)
    (hu : HasDerivAt (fun t => u t r) du s) :
    HasDerivAt
      (fun t => actualWholeRadiationLocalCubic (u t) r)
      (actualHartreeLocalCubicTimeVelocity (u s r) du) s := by
  have hRe := hartree_complex_curve_re_hasDerivAt
    (fun t => u t r) du s hu
  have hIm := hartree_complex_curve_im_hasDerivAt
    (fun t => u t r) du s hu
  have hReal : HasDerivAt
      (fun t => (u t r).re ^ 2 + (u t r).im ^ 2)
      (2 * ((u s r).re * du.re + (u s r).im * du.im)) s := by
    convert (hRe.pow 2).add (hIm.pow 2) using 1
    ring
  have hComplex := hReal.ofReal_comp
  have hProduct := hComplex.mul hu
  convert hProduct using 1
  · funext t
    dsimp [actualWholeRadiationLocalCubic]
    rw [← Complex.normSq_eq_norm_sq (u t r), Complex.normSq_apply]
    rfl
  · unfold actualHartreeLocalCubicTimeVelocity
    rw [← Complex.normSq_eq_norm_sq (u s r), Complex.normSq_apply]
    push_cast
    ring

end HBL.TypeIIDynamicSelection
