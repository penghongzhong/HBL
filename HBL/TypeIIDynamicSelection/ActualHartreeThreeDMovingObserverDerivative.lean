import HBL.HartreeSpatialCompletion
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Original 3D inverse-square Hartree potential: moving physical observer

The ORIGINAL convolution in R^3 has kernel |x-y|^(-2), and the
physical quartic density at one time s is |z(s,y)|^4. This is
not an arbitrary local model. The fixed-time spatial derivative of
the actual noncompact convolution was proved in
HartreeSpatialCompletion.potential_hasFDerivAt_of_core_approximation.

This theorem composes that genuine spatial derivative with the physical
moving observer x(t)=a(t)•x0. Neither the potential derivative nor a
blowup rate is assumed. The only inputs are the original density,
its genuine spatial gradient, a compactly supported smooth
approximation of BOTH, and explicit original L1/L∞ bounds.

This is the spatial-observer term at a FIXED physical density time.
An identification with the original half-line radial logarithmic
representation, its simultaneous time-varying source term, changing
Kummer basis, and full original 3D four-piece residual remain open.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.RegularRadiation
open HBL.RegularRadiation.SpatialCompletion

/-- The genuine original 3D quartic physical radiation density. -/
def actualHartreeThreeDQuarticRadiationDensity
    (z : ℝ → Space → ℂ) (s : ℝ) : Space → ℂ :=
  fun y => ((‖z s y‖ ^ 4 : ℝ) : ℂ)

/-- Moving spatial observer derivative of the original inverse-square
three-dimensional Riesz convolution, with the actual quartic
radiation density and no assumed differentiability of the potential. -/
theorem actual_Hartree_threeD_quartic_potential_moving_observer_hasDerivAt
    (z : ℝ → Space → ℂ) (s : ℝ)
    (a : ℝ → ℝ) (aDot : ℝ)
    (hA : HasDerivAt a aDot s) (x0 : Space)
    (D : Space → Space →L[ℝ] ℂ) (ρn : ℕ → Space → ℂ)
    (hc : ∀ n, HasCompactSupport (ρn n))
    (hn : ∀ n, ContDiff ℝ 1 (ρn n))
    (hρ : Integrable (actualHartreeThreeDQuarticRadiationDensity z s))
    (hD : Integrable D)
    (M0 M1 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hb0 : ∀ᵐ y : Space,
      ‖actualHartreeThreeDQuarticRadiationDensity z s y‖ ≤ M0)
    (hb1 : ∀ᵐ y : Space, ‖D y‖ ≤ M1)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (he0 : ∀ n, ∀ᵐ y : Space,
      ‖ρn n y - actualHartreeThreeDQuarticRadiationDensity z s y‖ ≤ ε n)
    (he1 : ∀ n, ∀ᵐ y : Space,
      ‖fderiv ℝ (ρn n) y - D y‖ ≤ ε n)
    (hi0 : ∀ n,
      (∫ y : Space,
        ‖ρn n y - actualHartreeThreeDQuarticRadiationDensity z s y‖) ≤ ε n)
    (hi1 : ∀ n,
      (∫ y : Space, ‖fderiv ℝ (ρn n) y - D y‖) ≤ ε n) :
    HasDerivAt
      (fun t => potential (actualHartreeThreeDQuarticRadiationDensity z s)
        ((a t) • x0))
      (gradientPotential D ((a s) • x0) (aDot • x0)) s := by
  have hSpatial :=
    potential_hasFDerivAt_of_core_approximation
      (actualHartreeThreeDQuarticRadiationDensity z s)
      D ρn hc hn hρ hD M0 M1 hM0 hM1 hb0 hb1
      ε hε hεlim he0 he1 hi0 hi1
  have hObserver :
      HasDerivAt (fun t => (a t) • x0) (aDot • x0) s :=
    hA.smul_const x0
  exact (hSpatial ((a s) • x0)).comp_hasDerivAt s hObserver

end HBL.TypeIIDynamicSelection
