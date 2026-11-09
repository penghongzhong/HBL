import HBL.TypeIIDynamicSelection.ActualHartreeBubbleSquaredPotentialDecay
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# Spatially sharp original Hartree Riesz potential under W^2 domination

The genuinely positive radial inverse-square logarithmic kernel and
the accepted exact W^2 row decay imply a spatially decaying bound
for any measurable physical source F with |F| <= C W^2.
No source is fabricated, and no time-order estimate is claimed.

This is required to integrate original nonlinear quartic density
remainders into the weighted Fredholm source spaces.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_true_Riesz_bubble_squared_dominated_spatial_decay
    (F : ℝ → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0 ≤ C)
    (hpoint : ∀ x : ℝ, 0 < x → |F x| ≤ C * bubble x ^ 2)
    (r : ℝ) (hr : 0 < r) :
    IntegrableOn
      (fun x => x * hartreeRadialLog r x * F x) (Ioi (0 : ℝ)) ∧
    |radialHartreePotential F r| ≤
      C * actualHartreeBubbleSquaredRieszDecayConstant / (1 + r) := by
  have hBase :=
    radialHartreePotential_bubble_sq_domination F hF hC hpoint hr
  have hRow := radialHartreeBubble_integrable_bound hr
  have hCoeff : 0 ≤ 2 * Real.pi * hartreeKappa / r := by
    unfold hartreeKappa
    positivity
  have hLog : Measurable (hartreeRadialLog r) := by
    unfold hartreeRadialLog
    fun_prop
  have hMeas :
      Measurable (fun x => x * hartreeRadialLog r x * F x) :=
    (measurable_id.mul hLog).mul hF
  have hPointwise (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      |x * hartreeRadialLog r x * F x| ≤
        C * (x * hartreeRadialLog r x * bubble x ^ 2) := by
    have hLogPos := hartreeRadialLog_nonneg r x hr hx
    rw [abs_mul, abs_mul, abs_of_pos hx, abs_of_nonneg hLogPos]
    calc
      x * hartreeRadialLog r x * |F x| ≤
        x * hartreeRadialLog r x * (C * bubble x ^ 2) :=
          mul_le_mul_of_nonneg_left (hpoint x hx)
            (mul_nonneg hx.le hLogPos)
      _ = _ := by ring
  have hIntegral :
      |∫ x in Ioi (0 : ℝ), x * hartreeRadialLog r x * F x| ≤
        C * (∫ x in Ioi (0 : ℝ),
          x * hartreeRadialLog r x * bubble x ^ 2) := by
    calc
      _ ≤ ∫ x in Ioi (0 : ℝ), |x * hartreeRadialLog r x * F x| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ x in Ioi (0 : ℝ),
          C * (x * hartreeRadialLog r x * bubble x ^ 2) := by
        apply integral_mono_ae hBase.1.abs (hRow.1.const_mul C)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hPointwise x hx
      _ = C * ∫ x in Ioi (0 : ℝ),
          x * hartreeRadialLog r x * bubble x ^ 2 := by
        rw [integral_const_mul]
  have hPotential :
      |radialHartreePotential F r| ≤
        C * radialHartreePotential (fun x => bubble x ^ 2) r := by
    unfold radialHartreePotential
    rw [abs_mul, abs_of_nonneg hCoeff]
    calc
      (2 * Real.pi * hartreeKappa / r) *
          |∫ x in Ioi (0 : ℝ),
            x * hartreeRadialLog r x * F x| ≤
        (2 * Real.pi * hartreeKappa / r) *
          (C * (∫ x in Ioi (0 : ℝ),
             x * hartreeRadialLog r x * bubble x ^ 2)) :=
        mul_le_mul_of_nonneg_left hIntegral hCoeff
      _ = C * ((2 * Real.pi * hartreeKappa / r) *
        (∫ x in Ioi (0 : ℝ),
            x * hartreeRadialLog r x * bubble x ^ 2)) := by ring
  have hSpatial := actual_Hartree_bubble_squared_Riesz_spatial_decay r hr
  refine ⟨hBase.1, hPotential.trans ?_⟩
  calc
    C * radialHartreePotential (fun x => bubble x ^ 2) r ≤
      C * (actualHartreeBubbleSquaredRieszDecayConstant / (1 + r)) :=
      mul_le_mul_of_nonneg_left hSpatial hC
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
