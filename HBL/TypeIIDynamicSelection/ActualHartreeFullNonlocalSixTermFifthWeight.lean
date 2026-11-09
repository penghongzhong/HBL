import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylorBubbleBound
import HBL.TypeIIDynamicSelection.ActualHartreeSixTermNonlocalFifthWeight
import HBL.TypeIIDynamicSelection.ActualHartreeHalfRadialCubicTaylorWeights
import Mathlib.Tactic

/-!
# Full ORIGINAL Hartree nonlocal Taylor remainder under actual Riesz row budgets

The exact original radial quartic inverse-square nonlocal Hartree
linearization produces six nonlinear products. Their fifth-weight
square is controlled by the THREE genuine original radial Riesz
potential source rows and the true local cubic Taylor polynomials.
No bound on the nonlinear remainder is postulated.

The displayed Riesz row estimates must be supplied by the actual
two-scale physical source (already being independently strictly audited);
no full PDE parametrix or temporal order follows from this local
fixed-slice source estimate alone.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_full_original_nonlocal_Taylor_six_term_fifth_weight
    (U H : ℝ → ℂ) (r : ℝ) (hr : 0 < r)
    (M K e A0 A1 AR : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hAR : 0 ≤ AR)
    (hU : ‖U r‖ ≤ M)
    (hHalf : (1+r)*‖U r‖^2 ≤ K)
    (hH : ‖H r‖ ≤ e)
    (hHweight : (1+r)*‖H r‖ ≤ 2*e)
    (h0 : IntegrableOn
       (fun x => x*hartreeRadialLog r x*‖U x‖^4) (Ioi (0:ℝ)))
    (h1 : IntegrableOn
       (fun x => x*hartreeRadialLog r x*
         actualHartreeComplexDensityLinear (U x) (H x)) (Ioi (0:ℝ)))
    (hR : IntegrableOn
       (fun x => x*hartreeRadialLog r x*
         actualHartreeComplexDensityRemainder (U x) (H x)) (Ioi (0:ℝ)))
    (hP0 : (1+r)*
       |radialHartreePotential (fun x => ‖U x‖^4) r| ≤ A0)
    (hP1 : (1+r)*
       |radialHartreePotential
         (fun x => actualHartreeComplexDensityLinear (U x) (H x)) r| ≤ A1)
    (hPR : (1+r)*
       |radialHartreePotential
         (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r| ≤ AR) :
    (1+r)^5*‖actualHartreeComplexTaylorRemainder U H r‖^2 ≤
      2*(AR^2*K^3+
        ((A0+A1+AR)*(6*K*e+4*(3*M+e)*e^2))^2) := by
  let t : ℝ := 1+r
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have hCubic :=
    actual_Hartree_half_radial_original_cubic_Taylor_weighted
      (U r) (H r) t M K e ht hM hK he
      hU hHalf hH hHweight
  have hP0C :
      t*‖(radialHartreePotential
        (fun x => ‖U x‖^4) r : ℂ)‖ ≤ A0 := by
    simpa only [t, Complex.norm_real,Real.norm_eq_abs] using hP0
  have hP1C :
      t*‖(radialHartreePotential
        (fun x => actualHartreeComplexDensityLinear (U x) (H x)) r : ℂ)‖
        ≤ A1 := by
    simpa only [t,Complex.norm_real,Real.norm_eq_abs] using hP1
  have hPRC :
      t*‖(radialHartreePotential
        (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r : ℂ)‖
        ≤ AR := by
    simpa only [t,Complex.norm_real,Real.norm_eq_abs] using hPR
  have hB1 : 0 ≤ 6*K*e := by positivity
  have hBR : 0 ≤ 4*(3*M+e)*e^2 := by positivity
  have hAlgebra :=
    actual_Hartree_six_original_nonlocal_Taylor_products_fifth_weight
      t A0 A1 AR (6*K*e) (4*(3*M+e)*e^2) K
      ht hA0 hA1 hAR hB1 hBR hK
      (radialHartreePotential (fun x => ‖U x‖^4) r : ℂ)
      (radialHartreePotential
        (fun x => actualHartreeComplexDensityLinear (U x) (H x)) r : ℂ)
      (radialHartreePotential
        (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r : ℂ)
      (actualHartreeComplexCubic (U r))
      (actualHartreeComplexCubicLinear (U r) (H r))
      (actualHartreeComplexCubicRemainder (U r) (H r))
      hP0C hP1C hPRC hCubic.1 hCubic.2.1 hCubic.2.2
  have hExact :=
    actual_Hartree_complex_Taylor_nonlocal_identity U H r h0 h1 hR
  rw [hExact]
  simpa only [t] using hAlgebra

end HBL.TypeIIDynamicSelection
