import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylor
import HBL.RadialHartreePotential
import Mathlib.Tactic

/-!
# Exact ORIGINAL quartic radial Hartree potential Taylor split

This module composes the previously proved actual complex quartic
Taylor identity with the genuine inverse-square radial Hartree
integral, retaining the quadratic nonlocal density potential.
Only explicit integrability of the three real original density terms
is used. There is no independent Riesz smallness, positive-time
order, prescribed speed, or external axiom.

This is a load-bearing source *identity* only. It does not assert
a weighted H1 estimate, nonlinear PDE residual gain, or §2.13.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole

/-- Additivity of the actual radial inverse-square Hartree convolution.
The integrability hypotheses refer to the real physical kernel. -/
theorem actual_Hartree_radial_original_potential_add
    (F G : ℝ → ℝ) (r : ℝ)
    (hF : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi (0 : ℝ)))
    (hG : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * G rho) (Ioi (0 : ℝ))) :
    radialHartreePotential (fun x => F x + G x) r =
      radialHartreePotential F r + radialHartreePotential G r := by
  have hEq :
      (fun rho : ℝ =>
        rho * hartreeRadialLog r rho * (F rho + G rho)) =
      (fun rho : ℝ =>
        rho * hartreeRadialLog r rho * F rho +
        rho * hartreeRadialLog r rho * G rho) := by
    funext rho
    ring
  unfold radialHartreePotential
  rw [hEq, integral_add hF hG]
  ring

/-- True fourth-degree Hartree density, split at the original real
profile into its linear and quadratic/higher pieces. -/
theorem actual_Hartree_original_quartic_Riesz_second_order_split
    (w : ℝ → ℝ) (u : ℝ → ℂ) (r : ℝ)
    (h0 : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(w rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (h1 : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualHartreeComplexDensityLinear (w rho : ℂ) (u rho))
      (Ioi (0 : ℝ)))
    (h2 : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualHartreeComplexDensityRemainder (w rho : ℂ) (u rho))
      (Ioi (0 : ℝ))) :
    radialHartreePotential
        (fun rho => ‖(w rho : ℂ) + u rho‖ ^ 4) r =
      radialHartreePotential (fun rho => ‖(w rho : ℂ)‖ ^ 4) r +
      radialHartreePotential
        (fun rho => actualHartreeComplexDensityLinear (w rho : ℂ) (u rho)) r +
      radialHartreePotential
        (fun rho => actualHartreeComplexDensityRemainder (w rho : ℂ) (u rho)) r := by
  let f0 : ℝ → ℝ := fun rho => ‖(w rho : ℂ)‖ ^ 4
  let f1 : ℝ → ℝ := fun rho =>
    actualHartreeComplexDensityLinear (w rho : ℂ) (u rho)
  let f2 : ℝ → ℝ := fun rho =>
    actualHartreeComplexDensityRemainder (w rho : ℂ) (u rho)
  have h01 : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        (f0 rho + f1 rho)) (Ioi (0 : ℝ)) := by
    have hEq :
        (fun rho : ℝ =>
          rho * hartreeRadialLog r rho * (f0 rho + f1 rho)) =
        (fun rho : ℝ =>
          rho * hartreeRadialLog r rho * f0 rho +
          rho * hartreeRadialLog r rho * f1 rho) := by
      funext rho
      ring
    rw [hEq]
    exact h0.add h1
  have hDensity :
      (fun rho : ℝ => ‖(w rho : ℂ) + u rho‖ ^ 4) =
        (fun rho => (f0 rho + f1 rho) + f2 rho) := by
    funext rho
    exact (actual_Hartree_complex_Taylor_polynomial_identity
      (w rho : ℂ) (u rho)).1
  rw [hDensity]
  calc
    radialHartreePotential
        (fun rho => (f0 rho + f1 rho) + f2 rho) r =
      radialHartreePotential (fun rho => f0 rho + f1 rho) r +
      radialHartreePotential f2 r :=
        actual_Hartree_radial_original_potential_add
          (fun rho => f0 rho + f1 rho) f2 r h01 h2
    _ = radialHartreePotential f0 r +
        radialHartreePotential f1 r + radialHartreePotential f2 r := by
      rw [actual_Hartree_radial_original_potential_add f0 f1 r h0 h1]

/-- Exact full ORIGINAL quartic Hartree nonlinear quadratic remainder,
including the complete Riesz potential and the genuine complex cubic.
The three hypotheses are only absolute convergence of the original
Riesz density rows; no quantitative source bound is postulated. -/
theorem actual_Hartree_full_original_nonlinear_quadratic_split
    (w : ℝ → ℝ) (u : ℝ → ℂ) (r : ℝ)
    (h0 : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(w rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (h1 : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualHartreeComplexDensityLinear (w rho : ℂ) (u rho))
      (Ioi (0 : ℝ)))
    (h2 : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualHartreeComplexDensityRemainder (w rho : ℂ) (u rho))
      (Ioi (0 : ℝ))) :
    let p0 := radialHartreePotential
      (fun rho => ‖(w rho : ℂ)‖ ^ 4) r
    let p1 := radialHartreePotential
      (fun rho => actualHartreeComplexDensityLinear
        (w rho : ℂ) (u rho)) r
    let p2 := radialHartreePotential
      (fun rho => actualHartreeComplexDensityRemainder
        (w rho : ℂ) (u rho)) r
    let pFull := radialHartreePotential
      (fun rho => ‖(w rho : ℂ) + u rho‖ ^ 4) r
    let q0 := actualHartreeComplexCubic (w r : ℂ)
    let q1 := actualHartreeComplexCubicLinear (w r : ℂ) (u r)
    let q2 := actualHartreeComplexCubicRemainder (w r : ℂ) (u r)
    (pFull : ℂ) * actualHartreeComplexCubic ((w r : ℂ) + u r) -
      ((p0 : ℂ) * q0 + ((p0 : ℂ) * q1 + (p1 : ℂ) * q0)) =
      (p0 : ℂ) * q2 + (p1 : ℂ) * (q1 + q2) +
        (p2 : ℂ) * actualHartreeComplexCubic ((w r : ℂ) + u r) := by
  have hp := actual_Hartree_original_quartic_Riesz_second_order_split
    w u r h0 h1 h2
  have hq := (actual_Hartree_complex_Taylor_polynomial_identity
    (w r : ℂ) (u r)).2
  dsimp only
  rw [hp, hq]
  push_cast
  ring


end HBL.TypeIIDynamicSelection
