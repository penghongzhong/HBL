import HBL.TypeIIDynamicSelection.ActualOneLayerTwoChannelPDE
import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import Mathlib.Tactic

/-!
# Exact first radial derivative and dilation for the REAL Hartree scaling

The physical high-regularity Hartree radiation has the critical pullback
Z_ell(r) = sqrt(ell) z(ell r).  Its radial derivative and the original
dilation generator are computed by the actual chain rule:
  (Z_ell)'(r) = sqrt(ell)*ell*z'(ell*r),
  Lambda(Z_ell)(r) = sqrt(ell)*Lambda(z)(ell*r).

No preset Type-II rate, abstract time derivative, or modeled dilation
is inserted. These identities are necessary to connect the cited
regular Hartree physical flow to the actual renormalized PDE residual.
The second spatial derivative and the entire time/phase chain rule
are separate next obligations.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual complex-valued radial critical pullback differentiates
with its genuine spatial Jacobian ell; no term is thrown away. -/
theorem actual_Hartree_critical_rescaled_radial_deriv
    (ell r : ℝ) (z : ℝ → ℂ)
    (hz : DifferentiableAt ℝ z (ell * r)) :
    deriv (rescalePhysicalRadiation ell z) r =
      ((Real.sqrt ell : ℂ) * ((ell : ℂ) * deriv z (ell * r))) := by
  have hscale : HasDerivAt (fun x : ℝ => ell * x) ell r :=
    hasDerivAt_const_mul ell
  have hc := hz.hasDerivAt.scomp r hscale
  have h := hc.const_mul (Real.sqrt ell : ℂ)
  change deriv (fun x : ℝ => (Real.sqrt ell : ℂ) * z (ell * x)) r = _
  convert h.deriv using 1
  · rfl

/-- The ORIGINAL radial dilation operator, including its 1/2
zero-order term, is exactly covariant under critical rescaling. -/
theorem actual_Hartree_critical_rescaled_dilation
    (ell r : ℝ) (z : ℝ → ℂ)
    (hz : DifferentiableAt ℝ z (ell * r)) :
    complexRadialDilation (rescalePhysicalRadiation ell z) r =
      (Real.sqrt ell : ℂ) *
        complexRadialDilation z (ell * r) := by
  unfold complexRadialDilation
  rw [actual_Hartree_critical_rescaled_radial_deriv ell r z hz]
  unfold rescalePhysicalRadiation
  push_cast
  ring

end HBL.TypeIIDynamicSelection
