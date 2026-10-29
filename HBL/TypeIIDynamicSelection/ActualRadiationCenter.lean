import HBL.RadialHartreeAmplitudeCenter
import Mathlib.Tactic

/-!
# The genuine whole-radiation slow monopole source of the Hartree equation

The source in the original manuscript is the quartic Hartree potential
at the origin of the ENTIRE rescaled radiation, not necessarily of a
remote component supported outside the moving monopole cutoff.

Under primitive radial amplitude hypotheses (measurability, boundedness,
finite physical radial mass, quadratic origin flatness), the actual
inverse-square Riesz integral gives a nonnegative scalar center coefficient
and a quantitative O(r^2) inner expansion. Its cubic interaction with the
ground-state bubble is likewise controlled. The coefficient is defined
from the full source and is not imposed as a terminal blowup speed.

This source estimate is a component of the physical one-layer construction;
it is not a proof of the actual coupled modulation system or Type II orbit.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The physical slow monopole coefficient at a fixed rescaled time,
obtained from the entire complex radial radiation density. -/
def actualRadiationCenter (Z : ℝ → ℂ) : ℝ :=
  radialHartreeCenter (fun rho => ‖Z rho‖ ^ 4)

/-- The genuine inverse-square center mass is nonnegative, as follows
from its full physical radial quartic-density integral. -/
theorem actualRadiationCenter_nonneg
    (Z : ℝ → ℂ) :
    0 ≤ actualRadiationCenter Z := by
  unfold actualRadiationCenter radialHartreeCenter
  have hc : 0 ≤ 4 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  exact mul_nonneg hc (integral_nonneg (fun rho => pow_nonneg (norm_nonneg (Z rho)) 4))

/-- The true rescaled Hartree radiation potential equals its output
center coefficient up to a quadratic spatial error on the bubble core.
No exterior support or artificial local cubic is introduced. -/
theorem actual_radiation_center_quadratic_bound
    (Z : ℝ → ℂ) {M D : ℝ}
    (hZ : Measurable Z) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbound : ∀ rho, 0 ≤ rho → ‖Z rho‖ ≤ M)
    (hmass : IntegrableOn (fun rho => rho ^ 2 * ‖Z rho‖ ^ 2) (Ioi 0))
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 →
      ‖Z rho - Z 0‖ ≤ D * rho ^ 2)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    |radialHartreePotential (fun rho => ‖Z rho‖ ^ 4) r -
        actualRadiationCenter Z| ≤
      radialHartreeCenterBoundConstant
        (fun rho => ‖Z rho‖ ^ 4) (4 * M ^ 3 * D) * r ^ 2 := by
  have hh := radialHartreeAmplitude_full_center_environment
    hZ hM hD hbound hmass hflat
  simpa only [actualRadiationCenter, radialHartreeCenter] using
    (hh.2.2.2.2.1 r hr hr1).2

/-- Consequently the ACTUAL self-radiation Hartree nonlocal term
multiplying the bubble cubic has a genuine O(r^2) center error.
The scalar coefficient is output by the full complex radiation. -/
theorem actual_radiation_center_bubble_cubic_error
    (Z : ℝ → ℂ) {M D : ℝ}
    (hZ : Measurable Z) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbound : ∀ rho, 0 ≤ rho → ‖Z rho‖ ≤ M)
    (hmass : IntegrableOn (fun rho => rho ^ 2 * ‖Z rho‖ ^ 2) (Ioi 0))
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 →
      ‖Z rho - Z 0‖ ≤ D * rho ^ 2)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖((radialHartreePotential (fun rho => ‖Z rho‖ ^ 4) r -
        actualRadiationCenter Z : ℝ) : ℂ) * (bubble r : ℂ) ^ 3‖ ≤
      radialHartreeCenterBoundConstant
        (fun rho => ‖Z rho‖ ^ 4) (4 * M ^ 3 * D) * r ^ 2 := by
  have hp := actual_radiation_center_quadratic_bound
    Z hZ hM hD hbound hmass hflat hr hr1
  have hb : ‖((bubble r : ℂ) ^ 3)‖ ≤ 1 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg _) (bubble_abs_le_one r) 3).trans
      (by norm_num)
  have hc : 0 ≤ radialHartreeCenterBoundConstant
      (fun rho => ‖Z rho‖ ^ 4) (4 * M ^ 3 * D) * r ^ 2 := by
    have hC := radialHartreeCenterBoundConstant_pos
      (fun rho => ‖Z rho‖ ^ 4)
      (show 0 ≤ 4 * M ^ 3 * D by positivity)
    positivity
  calc
    _ = |radialHartreePotential (fun rho => ‖Z rho‖ ^ 4) r -
          actualRadiationCenter Z| * ‖((bubble r : ℂ) ^ 3)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (radialHartreeCenterBoundConstant
           (fun rho => ‖Z rho‖ ^ 4) (4 * M ^ 3 * D) * r ^ 2) * 1 :=
      mul_le_mul hp hb (norm_nonneg _) hc
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
