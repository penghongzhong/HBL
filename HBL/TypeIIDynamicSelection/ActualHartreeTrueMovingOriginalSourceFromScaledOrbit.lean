import HBL.TypeIIDynamicSelection.ActualHartreeCriticalScaledInteraction
import HBL.TypeIIDynamicSelection.ActualHartreeFullInteractionTimeFromOrbit
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Eliminate the moving-observer Riesz derivative from the ORIGINAL Hartree F0

The previously verified original nonlinear interaction has exact
critical scaling, WITHOUT a local replacement:
  sqrt(a(t)) * F0(t,r)
    = Interaction(V_crit(t),Z_crit(t))(r),
where F0(t,r)=a(t)^2*Interaction(V_ell,c,z_ell)(a(t)*r).
The right-hand side is evaluated at FIXED normalized Kummer radius r;
the real/complex time varying scaled fields stay genuine.

Its time derivative is produced using the already verified
three-potential Hartree original Riesz derivative theorem for one
real-core/complex-radiation orbit, under primitive original density
derivative and dominating-integral bounds.

This file derives the derivative of F0(t,r) from the derivative of
that fixed-radius genuine scaled source and the scalar scale rate
a'(t). It does NOT assume HasDerivAt F0 as a premise and does NOT
postulate any Type-II speed. The source's high-regularity input
must still be produced along the final physical Hartree orbit.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeTrueCriticallyScaledOriginalInteraction
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (t r : ℝ) : ℂ :=
  actualOneLayerInteractionOnly
    (fun _ : ℝ =>
      actualHartreeCriticalScaledRealCore (a t)
        (monopolePerturbedRadialProfile
          (monopoleQuadraticRadius (c t)) (c t)))
    (fun _ : ℝ =>
      rescalePhysicalRadiation (a t)
        (rescalePhysicalRadiation (ell t) (z t))) 0 r

/-- The genuine moving physical Hartree Kummer source derivative comes
from its fixed-observer critically scaled source derivative. No
assumption of differentiability of the original F0(t,r) occurs. -/
theorem actual_Hartree_original_moving_source_derivative_from_scaled_orbit
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (s r adot : ℝ) (hA : HasDerivAt a adot s)
    (ha : 0 < a s) (scaledDot : ℂ)
    (hScaled : HasDerivAt
      (fun t => actualHartreeTrueCriticallyScaledOriginalInteraction
        a ell c z t r) scaledDot s) :
    HasDerivAt
      (fun t => actualHartreeLaplacianScaledKummerSource
        (a t) (ell t) (c t) (z t) r)
      (-( ((adot / (2 * Real.sqrt (a s)) : ℝ) : ℂ) /
            (((Real.sqrt (a s) : ℝ) : ℂ) ^ 2)) *
          actualHartreeTrueCriticallyScaledOriginalInteraction a ell c z s r +
        (((Real.sqrt (a s) : ℝ) : ℂ)⁻¹) * scaledDot) s := by
  have hSqrt : HasDerivAt
      (fun t => Real.sqrt (a t))
      (adot / (2 * Real.sqrt (a s))) s :=
    hA.sqrt ha.ne'
  have hSC : ((Real.sqrt (a s) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  have hSqrtC := hSqrt.ofReal_comp
  have hInv := hSqrtC.inv hSC
  have hProd :=
    hInv.mul hScaled
  have hAPos : ∀ᶠ t in 𝓝 s, 0 < a t :=
    hA.continuousAt.eventually (Ioi_mem_nhds ha)
  have hIdentity :
      (fun t => actualHartreeLaplacianScaledKummerSource
        (a t) (ell t) (c t) (z t) r) =ᶠ[𝓝 s]
      (fun t => (((Real.sqrt (a t) : ℝ) : ℂ)⁻¹) *
        actualHartreeTrueCriticallyScaledOriginalInteraction
          a ell c z t r) := by
    filter_upwards [hAPos] with t ht
    have hScale :=
      actual_Hartree_critical_scaled_selected_original_source
        (a t) (ell t) (c t) r ht (z t)
    have htSC : ((Real.sqrt (a t) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 ht).ne'
    calc
      actualHartreeLaplacianScaledKummerSource
          (a t) (ell t) (c t) (z t) r =
        (((Real.sqrt (a t) : ℝ) : ℂ)⁻¹) *
          (((Real.sqrt (a t) : ℝ) : ℂ) *
            actualHartreeLaplacianScaledKummerSource
              (a t) (ell t) (c t) (z t) r) := by
                field_simp [htSC]
      _ = (((Real.sqrt (a t) : ℝ) : ℂ)⁻¹) *
          actualHartreeTrueCriticallyScaledOriginalInteraction
            a ell c z t r := by rw [hScale]; rfl
  have hResult := hProd.congr_of_eventuallyEq hIdentity
  convert hResult using 1
  simp only [Pi.inv_apply]
  ring

end HBL.TypeIIDynamicSelection
