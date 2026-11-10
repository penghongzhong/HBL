import HBL.TypeIIDynamicSelection.ActualHartreeInnerSpectralC2PlateauSourceLock
import Mathlib.Tactic

/-!
# Original Hartree/Kummer inner backward-Volterra radial conjugation

The exact physical two-channel operator contains the nontrivial
\(2/y+i\,y/(2a^2)\) drift and the same complex spectral coefficient Q.
The radial substitution h=y e cancels its radial 2/y term exactly;
the remaining Q-i/2 shift is NOT omitted.  This statement is the
differential-algebra interface to the real original-source plateau
cancellation, not an assumed Volterra inverse or physical time gain.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- Radial \(h=y e\) conjugation of the original scaled physical Kummer
operator.  Both the imaginary transport coefficient and the correction
\(-i/2\) to the zero-order coefficient are determined by differentiation,
not assumed.  No source, decay order or blowup exponent is prescribed. -/
theorem actual_Hartree_backward_original_radial_conjugation
    (a r : ℝ) (ha : a ≠ 0) (hr : r ≠ 0)
    (Q : ℂ) (e : ℝ → ℂ)
    (he : ∀ x : ℝ, DifferentiableAt ℝ e x)
    (he2 : DifferentiableAt ℝ (deriv e) r) :
    let h : ℝ → ℂ := fun y => (y : ℂ) * e y
    deriv (deriv h) r +
        (Complex.I * (r : ℂ) / (2 * (a : ℂ) ^ 2)) * deriv h r +
        ((Q - Complex.I / 2) / (a : ℂ) ^ 2) * h r =
      (r : ℂ) *
        (deriv (deriv e) r +
          ((2 : ℂ) / (r : ℂ) +
            Complex.I * (r : ℂ) / (2 * (a : ℂ) ^ 2)) * deriv e r +
          (Q / (a : ℂ) ^ 2) * e r) := by
  dsimp only
  let h : ℝ → ℂ := fun y => (y : ℂ) * e y
  have hcast (x : ℝ) :
      HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using ((hasDerivAt_id x).ofReal_comp)
  have hfirst (x : ℝ) :
      HasDerivAt h (e x + (x : ℂ) * deriv e x) x := by
    change HasDerivAt (fun y : ℝ => (y : ℂ) * e y)
      (e x + (x : ℂ) * deriv e x) x
    convert (hcast x).mul ((he x).hasDerivAt) using 1
    ring
  have hnear :
      deriv h =ᶠ[𝓝 r] (fun x => e x + (x : ℂ) * deriv e x) := by
    filter_upwards with x
    exact (hfirst x).deriv
  have hmodel :
      HasDerivAt (fun x => e x + (x : ℂ) * deriv e x)
        (2 * deriv e r + (r : ℂ) * deriv (deriv e) r) r := by
    convert ((he r).hasDerivAt).add
      ((hcast r).mul he2.hasDerivAt) using 1
    ring
  have hsecond :
      HasDerivAt (deriv h)
        (2 * deriv e r + (r : ℂ) * deriv (deriv e) r) r :=
    hmodel.congr_of_eventuallyEq hnear
  rw [hsecond.deriv, (hfirst r).deriv]
  change (2 : ℂ) * deriv e r + (r : ℂ) * deriv (deriv e) r +
      Complex.I * (r : ℂ) / (2 * (a : ℂ)^2) *
        (e r + (r : ℂ) * deriv e r) +
      (Q - Complex.I / 2) / (a : ℂ)^2 * ((r : ℂ) * e r) =
    (r : ℂ) *
       (deriv (deriv e) r +
        ((2 : ℂ) / (r : ℂ) +
          Complex.I * (r : ℂ) / (2 * (a : ℂ)^2)) * deriv e r +
        Q / (a : ℂ)^2 * e r)
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  field_simp [haC, hrC]
  ring

end HBL.TypeIIDynamicSelection
