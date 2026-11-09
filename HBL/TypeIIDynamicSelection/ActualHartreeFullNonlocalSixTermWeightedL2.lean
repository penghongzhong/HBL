import HBL.TypeIIDynamicSelection.ActualHartreeFullNonlocalSixTermFifthWeight
import HBL.TypeIIDynamicSelection.ActualHartreeTrueQuadraticRieszCubicWeightedL2
import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleRadialDecay
import Mathlib.Tactic

/-!
# Full ORIGINAL inverse-square quartic Hartree Taylor in native weighted L2

The same physical nonlinear Taylor remainder, comprising ALL six Riesz
potential/cubic products, has a complete native L^(2,7/4) estimate
deduced from explicit ORIGINAL Riesz-row integrability and inverse-radius
bounds. No positive source order or nonlinear remainder bound is input.

The three row bounds and pointwise half-radial field controls are visible
assumptions here; physical source producers must instantiate them.
The full four-zone Hartree correction, dynamic parameter motion, and
original PDE linear principal cancellation remain unresolved.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_full_original_six_term_native_weighted_L2_from_Riesz_rows
    (U H : ℝ → ℂ)
    (hFMeas : Measurable (actualHartreeComplexTaylorRemainder U H))
    (M K e A0 A1 AR : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hAR : 0 ≤ AR)
    (hU : ∀ r : ℝ, 0 < r → ‖U r‖ ≤ M)
    (hHalf : ∀ r : ℝ, 0 < r → (1+r)*‖U r‖^2 ≤ K)
    (hH : ∀ r : ℝ, 0 < r → ‖H r‖ ≤ e*bubble r)
    (h0 : ∀ r : ℝ, 0 < r →
      IntegrableOn
        (fun x => x*hartreeRadialLog r x*‖U x‖^4) (Ioi (0:ℝ)))
    (h1 : ∀ r : ℝ, 0 < r →
      IntegrableOn
        (fun x => x*hartreeRadialLog r x*
          actualHartreeComplexDensityLinear (U x) (H x)) (Ioi (0:ℝ)))
    (hR : ∀ r : ℝ, 0 < r →
      IntegrableOn
        (fun x => x*hartreeRadialLog r x*
          actualHartreeComplexDensityRemainder (U x) (H x)) (Ioi (0:ℝ)))
    (hP0 : ∀ r : ℝ, 0 < r →
      (1+r)*|radialHartreePotential
        (fun x => ‖U x‖^4) r| ≤ A0)
    (hP1 : ∀ r : ℝ, 0 < r →
      (1+r)*|radialHartreePotential
        (fun x => actualHartreeComplexDensityLinear (U x) (H x)) r| ≤ A1)
    (hPR : ∀ r : ℝ, 0 < r →
      (1+r)*|radialHartreePotential
        (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r| ≤ AR) :
    let R : ℝ → ℂ := actualHartreeComplexTaylorRemainder U H
    let Q : ℝ := 2*(AR^2*K^3+
        ((A0+A1+AR)*(6*K*e+4*(3*M+e)*e^2))^2)
    MemLp (fun r : ℝ =>
      affineJapaneseWeight (7/4:ℝ) r*‖R r‖) 2 halfLineMeasure ∧
    (∫ r in Ioi (0:ℝ),
      (affineJapaneseWeight (7/4:ℝ) r*‖R r‖)^2) ≤
        Q*(∫ r in Ioi (0:ℝ), (1+r)^(-(3/2:ℝ))) := by
  dsimp only
  let R : ℝ → ℂ := actualHartreeComplexTaylorRemainder U H
  let Q : ℝ := 2*(AR^2*K^3+
      ((A0+A1+AR)*(6*K*e+4*(3*M+e)*e^2))^2)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hFive (r : ℝ) (hr : 0 < r) :
      (1+r)^5*‖R r‖^2 ≤ Q := by
    have hWB : bubble r ≤ 1 := bubble_le_one r
    have hHB : ‖H r‖ ≤ e := by
      calc
        _ ≤ e*bubble r := hH r hr
        _ ≤ e*1 := mul_le_mul_of_nonneg_left hWB he
        _ = e := mul_one e
    have hTwo : (1+r)*bubble r ≤ 2 := by
      have hRad := actual_one_orbit_bubble_le_inverse_radius r hr
      have hrB : r*bubble r ≤ 1 := by
        calc
          _ ≤ r*(1/r) :=
            mul_le_mul_of_nonneg_left hRad hr.le
          _ = 1 := by field_simp [hr.ne']
      calc
        (1+r)*bubble r = bubble r+r*bubble r := by ring
        _ ≤ 1+1 := add_le_add hWB hrB
        _ = 2 := by norm_num
    have hHweight : (1+r)*‖H r‖ ≤ 2*e := by
      calc
        _ ≤ (1+r)*(e*bubble r) :=
          mul_le_mul_of_nonneg_left (hH r hr) (by linarith)
        _ = e*((1+r)*bubble r) := by ring
        _ ≤ e*2 := mul_le_mul_of_nonneg_left hTwo he
        _ = 2*e := by ring
    have hSource :=
      actual_Hartree_full_original_nonlocal_Taylor_six_term_fifth_weight
        U H r hr M K e A0 A1 AR
        hM hK he hA0 hA1 hAR
        (hU r hr) (hHalf r hr) hHB hHweight
        (h0 r hr) (h1 r hr) (hR r hr)
        (hP0 r hr) (hP1 r hr) (hPR r hr)
    simpa only [R,Q] using hSource
  have hNative :=
    actual_Hartree_fifth_weight_square_to_original_weighted_L2
      R hFMeas Q hQ hFive
  simpa only [R,Q] using hNative

end HBL.TypeIIDynamicSelection
