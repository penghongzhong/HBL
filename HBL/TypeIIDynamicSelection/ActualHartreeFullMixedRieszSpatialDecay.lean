import HBL.TypeIIDynamicSelection.ActualHartreeMixedRieszRelativeBubbleSq
import HBL.TypeIIDynamicSelection.ActualHartreeBubbleSquaredPotentialDecay
import Mathlib.Tactic

/-!
# HBL revised 2.13: real complete mixed-quartic Hartree Riesz potential
# gains the true global inverse-radius tail, without a blowup-rate hypothesis

The original inverse-square radial Hartree kernel was never replaced.
Strictly audited positivity gives the SAME complete physical mixed
density's potential |I(Fmix)(r)| <= D sqrt(ell) I(W^2)(r).
The scalar source bridge controls I(W^2)(r) by C/(1+r).

This directly yields
  |I(Fmix)(r)| <= D C sqrt(ell)/(1+r),
for every physical r>0 and every 0<ell<=1, uniformly under the usual
high-regularity radial L-infinity and Strauss interfaces. It retains
all linear, quadratic and cubic quartic cross terms, the genuine
moment-selected moving monopole V_c, and exact Hartree Riesz potential.

The result is a REAL nonlinear source estimate, not a substitute for
the full local cubic, physical modulation derivatives, moving cutoff,
Frobenius boundary matching, finite-profile recursion, or dynamical
Type-II blowup solution. Nothing here imposes the time rate ell(t).
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The complete true physical Hartree mixed-quartic inverse-square
Riesz potential retains a global 1/(1+r) decay with explicit positive
critical physical-length gain O(sqrt(ell)). No bubble/cubic surrogate
or prescribed Type-II speed is introduced. -/
theorem actual_Hartree_full_mixed_Riesz_spatial_decay
    (ell c r B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hr : 0 < r) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    |radialHartreePotential
      (actualWholeRadiationMixedQuartic
        (monopolePerturbedRadialProfile
          (monopoleQuadraticRadius c) c)
        (rescalePhysicalRadiation ell z)) r| ≤
      ((4 * (2 + 9 * monopoleRadialBoundConstant) ^ 3 *
          (2 * (B + A)) +
        6 * (2 + 9 * monopoleRadialBoundConstant) ^ 2 *
          (2 * (B + A)) ^ 2 +
        4 * (2 + 9 * monopoleRadialBoundConstant) *
          (2 * (B + A)) ^ 3) *
        actualHartreeBubbleSquaredRieszDecayConstant) *
        Real.sqrt ell / (1 + r) := by
  let D : ℝ :=
    4 * (2 + 9 * monopoleRadialBoundConstant) ^ 3 *
        (2 * (B + A)) +
    6 * (2 + 9 * monopoleRadialBoundConstant) ^ 2 *
        (2 * (B + A)) ^ 2 +
    4 * (2 + 9 * monopoleRadialBoundConstant) *
        (2 * (B + A)) ^ 3
  have hD : 0 ≤ D := by
    dsimp [D]
    have hMon := monopoleRadialBoundConstant_pos
    positivity
  have hRel :
      |radialHartreePotential
        (actualWholeRadiationMixedQuartic
          (monopolePerturbedRadialProfile
            (monopoleQuadraticRadius c) c)
          (rescalePhysicalRadiation ell z)) r| ≤
        (D * Real.sqrt ell) *
          radialHartreePotential
            (fun rho => bubble rho ^ 2) r := by
    simpa only [D, mul_assoc] using
      (actual_Hartree_full_mixed_Riesz_relative_bubble_sq
        ell c r B A hell hellOne hr hc hB hA
        z hz hSup hStrauss)
  have hScalar :=
    actual_Hartree_bubble_squared_Riesz_spatial_decay r hr
  have hFactor : 0 ≤ D * Real.sqrt ell :=
    mul_nonneg hD (Real.sqrt_nonneg ell)
  calc
    |radialHartreePotential
        (actualWholeRadiationMixedQuartic
          (monopolePerturbedRadialProfile
            (monopoleQuadraticRadius c) c)
          (rescalePhysicalRadiation ell z)) r| ≤
      (D * Real.sqrt ell) *
        radialHartreePotential
          (fun rho => bubble rho ^ 2) r := hRel
    _ ≤ (D * Real.sqrt ell) *
        (actualHartreeBubbleSquaredRieszDecayConstant / (1 + r)) :=
      mul_le_mul_of_nonneg_left hScalar hFactor
    _ = (D * actualHartreeBubbleSquaredRieszDecayConstant) *
        Real.sqrt ell / (1 + r) := by ring
    _ = _ := rfl

end HBL.TypeIIDynamicSelection
