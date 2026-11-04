import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylorBubbleBound
import HBL.MonopoleComplexResidual
import Mathlib.Tactic

/-!
# Actual Hartree PDE residual after a complex correction

The background and correction are genuine complex radial fields. The
renormalized residual, radial derivatives and Hartree linearization are
the original physical expressions. Both modulation increments and their
cross terms with the correction remain in the identity.

This is a formula for the complete new residual. It does not assume that
the correction solves the linearized equation, that its moving interfaces
match, or that the new residual has a better time order.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The complete differential and first Hartree variation, including both
speed increments acting on the background and on the correction. -/
def actualHartreeComplexCorrectionLinearPart
    (U H : ℝ → ℝ → ℂ) (b omega db domega s r : ℝ) : ℂ :=
  Complex.I * deriv (fun t => H t r) s +
    complexRadialLaplacian (H s) r +
    actualHartreeComplexLinearization (U s) (H s) r +
    Complex.I * (b : ℂ) * complexRadialDilation (H s) r +
    (omega : ℂ) * H s r +
    Complex.I * (db : ℂ) * complexRadialDilation (U s) r +
    (domega : ℂ) * U s r +
    Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
    (domega : ℂ) * H s r

/-- Exact correction identity for the original complex Hartree PDE.
Every differentiated sum is justified on a positive-radius neighborhood;
no cancellation or size estimate for the linear part is an input. -/
theorem actual_Hartree_complex_correction_residual_exact
    (U H : ℝ → ℝ → ℂ) (b omega db domega s r : ℝ)
    (hr : 0 < r)
    (hUtime : DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r) :
    complexRadialRenormalizedResidual
        (fun t x => U t x + H t x) (b + db) (omega + domega) s r -
      complexRadialRenormalizedResidual U b omega s r =
      actualHartreeComplexCorrectionLinearPart U H b omega db domega s r +
        actualHartreeComplexTaylorRemainder (U s) (H s) r := by
  have htime :
      deriv (fun t => U t r + H t r) s =
        deriv (fun t => U t r) s + deriv (fun t => H t r) s :=
    (hUtime.hasDerivAt.add hHtime.hasDerivAt).deriv
  have hfirst :
      deriv (fun x => U s x + H s x) r =
        deriv (U s) r + deriv (H s) r :=
    ((hUspace r hr).hasDerivAt.add (hHspace r hr).hasDerivAt).deriv
  have hfirst_near :
      deriv (fun x => U s x + H s x) =ᶠ[𝓝 r]
        (fun x => deriv (U s) x + deriv (H s) x) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact ((hUspace x hx).hasDerivAt.add (hHspace x hx).hasDerivAt).deriv
  have hsecond :
      deriv (deriv (fun x => U s x + H s x)) r =
        deriv (deriv (U s)) r + deriv (deriv (H s)) r :=
    ((hUsecond.hasDerivAt.add hHsecond.hasDerivAt).congr_of_eventuallyEq
      hfirst_near).deriv
  have hlaplacian :
      complexRadialLaplacian (fun x => U s x + H s x) r =
        complexRadialLaplacian (U s) r + complexRadialLaplacian (H s) r := by
    unfold complexRadialLaplacian
    rw [hsecond, hfirst]
    ring
  have hdilation :
      complexRadialDilation (fun x => U s x + H s x) r =
        complexRadialDilation (U s) r + complexRadialDilation (H s) r := by
    unfold complexRadialDilation
    rw [hfirst]
    ring
  unfold complexRadialRenormalizedResidual
  rw [htime, hlaplacian, hdilation]
  unfold actualHartreeComplexCorrectionLinearPart actualHartreeComplexTaylorRemainder
  push_cast
  ring

/-- The actual PDE residual after removal of its displayed differential
and first-variation terms has a quadratic Hartree bound. The bubble
envelopes imply convergence of the genuine nonlocal rows in the Taylor
estimate; no unweighted L2 assumption or residual-order hypothesis is used. -/
theorem actual_Hartree_complex_correction_residual_quadratic
    (U H : ℝ → ℝ → ℂ) (b omega db domega s r : ℝ)
    (hr : 0 < r)
    (hUtime : DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r)
    (hUmeas : Measurable (U s)) (hHmeas : Measurable (H s))
    (M e : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hUB : ∀ rho : ℝ, 0 < rho → ‖U s rho‖ ≤ M * bubble rho)
    (hHB : ∀ rho : ℝ, 0 < rho → ‖H s rho‖ ≤ e * bubble rho) :
    ‖complexRadialRenormalizedResidual
        (fun t x => U t x + H t x) (b + db) (omega + domega) s r -
      complexRadialRenormalizedResidual U b omega s r -
      actualHartreeComplexCorrectionLinearPart U H b omega db domega s r‖ ≤
      63 * (M + e) ^ 5 * e ^ 2 * bubble r ^ 5 := by
  rw [actual_Hartree_complex_correction_residual_exact
    U H b omega db domega s r hr hUtime hHtime hUspace hHspace hUsecond hHsecond,
    add_sub_cancel_left]
  exact actual_Hartree_complex_Taylor_bubble_bound
    (U s) (H s) hUmeas hHmeas M e hM he hUB hHB r hr

end HBL.TypeIIDynamicSelection
