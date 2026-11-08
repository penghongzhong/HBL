import HBL.TypeIIDynamicSelection.ActualHartreeCriticalScaledInteraction
import HBL.TypeIIDynamicSelection.ActualHartreeScaledPhaseSourceTangent
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Actual Hartree two-stage critically scaled CORE time derivative

The real core of the actual original mixed Riesz Kummer source after
critical scaling is literally
  V_a,c(s,r)=sqrt(a(s))*V_{c(s)}(a(s)*r),
with V_c the genuine cutoff monopole, not a synthetic profile.

We reuse the already verified joint c-parameter and spatial derivative
of the actual cutoff monopole. It is valid through c=0, where the
absolute value in the cutoff is not separately differentiable; the
genuine source is differentiable due to the physical cancellation.

The derivative is derived directly from a'(s), c'(s), not inserted
as a separate field-regularity assumption. No Type-II blowup rate
is prescribed. This closes the real core tangent needed to instantiate
the original full three-Riesz Hartree source time derivative on
the actual scaled orbit. The complex radiation tangent and original
quartic velocity majorants remain distinct analytic producer tasks.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_two_stage_critical_core_time_hasDerivAt
    (a c : ℝ → ℝ) (s r adot cdot : ℝ)
    (ha : HasDerivAt a adot s)
    (hc : HasDerivAt c cdot s)
    (hapos : 0 < a s) (hr : 0 < r) :
    HasDerivAt
      (fun t => actualHartreeCriticalScaledRealCore
        (a t) (actualMomentLockedCore (c t)) r)
      ((adot / (2 * Real.sqrt (a s))) *
          actualMomentLockedCore (c s) (a s * r) +
        Real.sqrt (a s) *
          actualMomentLockedCoreTotalTangent
            (c s) (a s * r) cdot (adot * r)) s := by
  have hArg : HasDerivAt (fun t => a t * r) (adot * r) s :=
    ha.mul_const r
  have hCore :=
    actual_Hartree_moment_locked_core_joint_hasDerivAt
      c (fun t => a t * r) hc hArg (mul_pos hapos hr)
  have hRoot : HasDerivAt (fun t => Real.sqrt (a t))
      (adot / (2 * Real.sqrt (a s))) s := ha.sqrt hapos.ne'
  have hProd := hRoot.mul hCore
  convert hProd using 1
  · funext t
    rfl
  · ring

end HBL.TypeIIDynamicSelection
