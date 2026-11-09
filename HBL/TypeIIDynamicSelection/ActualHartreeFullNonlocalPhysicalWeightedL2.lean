import HBL.TypeIIDynamicSelection.ActualHartreeFullNonlocalSixTermWeightedL2
import HBL.TypeIIDynamicSelection.ActualHartreeHalfRadialOriginalRieszLinear
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceQuadraticRieszSpatialDecay
import HBL.TypeIIDynamicSelection.ActualHartreeRieszMeasurability
import Mathlib.Tactic

/-!
# ALL six true inverse-square quartic Hartree Taylor terms in native weighted L2

No three-Riesz-row estimate, independent nonlinear source majorant or
positive temporal order is assumed. The TRUE ORIGINAL logarithmic radial
potential of the background density, its real-linear variation, and
the full quadratic density remainder is produced from arbitrary measurable
complex U,H with physically valid uniform L-infinity, half-radial U,
and bubble-small H. The exact nonlinear Taylor identity gives a genuine six-term native
L^(2,7/4) estimate, but this LEGACY theorem's coarse numerical constant
has a spurious A0*B1=O(e) contribution: it proves only O(e) for the
norm, not O(e^2). For the genuinely quadratic coefficient and its
complete physically sourced proof use
ActualHartreeFullNonlocalPhysicalWeightedL2Sharp. No missing source
bound is silently assumed here.

The physical four-piece Fredholm/Kummer correction must still be
constructed and shown to meet these field/velocity estimates, solve
the real principal linearized PDE, and be directly parameter Lipschitz.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The original nonlocal Hartree Taylor remainder is measurable
without declaring any separate abstract nonlinear source. -/
theorem actual_Hartree_complex_original_nonlinear_Taylor_measurable
    (U H : ℝ → ℂ)
    (hUmeas : Measurable U) (hHmeas : Measurable H) :
    Measurable (actualHartreeComplexTaylorRemainder U H) := by
  have hAdd : Measurable (fun r => U r+H r) := hUmeas.add hHmeas
  have hNAdd := actual_complexRadialHartreeNonlinearity_measurable _ hAdd
  have hNU := actual_complexRadialHartreeNonlinearity_measurable U hUmeas
  have hP0 := actual_radialHartreePotential_measurable
    (fun x => ‖U x‖^4) (hUmeas.norm.pow_const 4)
  have hD1 : Measurable
      (fun x => actualHartreeComplexDensityLinear (U x) (H x)) := by
    unfold actualHartreeComplexDensityLinear actualHartreeComplexRealPair
    fun_prop
  have hP1 := actual_radialHartreePotential_measurable
    (fun x => actualHartreeComplexDensityLinear (U x) (H x)) hD1
  have hC0 : Measurable
      (fun r => actualHartreeComplexCubic (U r)) := by
    unfold actualHartreeComplexCubic
    fun_prop
  have hC1 : Measurable
      (fun r => actualHartreeComplexCubicLinear (U r) (H r)) := by
    unfold actualHartreeComplexCubicLinear actualHartreeComplexRealPair
    fun_prop
  have hLinear : Measurable (actualHartreeComplexLinearization U H) := by
    unfold actualHartreeComplexLinearization
    exact ((Complex.measurable_ofReal.comp hP0).mul hC1).add
      ((Complex.measurable_ofReal.comp hP1).mul hC0)
  unfold actualHartreeComplexTaylorRemainder
  exact (hNAdd.sub hNU).sub hLinear

/-- Complete ORIGINAL Hartree nonlocal source: no missing Riesz products.
The displayed hypotheses are primitive physical field bounds only.
The output is in the manuscript's actual Fredholm weighted L2 space. -/
theorem actual_Hartree_full_original_six_term_nonlinear_weighted_L2
    (U H : ℝ → ℂ)
    (hUmeas : Measurable U) (hHmeas : Measurable H)
    (M K e : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hU : ∀ r : ℝ, 0 < r → ‖U r‖ ≤ M)
    (hHalf : ∀ r : ℝ, 0 < r → (1+r)*‖U r‖^2 ≤ K)
    (hH : ∀ r : ℝ, 0 < r → ‖H r‖ ≤ e*bubble r) :
    let C : ℝ := actualHartreeBubbleSquaredRieszDecayConstant
    let A0 : ℝ := K^2*C
    let A1 : ℝ := (8*M*K*e)*C
    let AR : ℝ := ((6*M^2+4*M*e+e^2)*e^2)*C
    let Q : ℝ := 2*(AR^2*K^3+
      ((A0+A1+AR)*(6*K*e+4*(3*M+e)*e^2))^2)
    let R : ℝ → ℂ := actualHartreeComplexTaylorRemainder U H
    MemLp (fun r : ℝ =>
      affineJapaneseWeight (7/4:ℝ) r*‖R r‖) 2 halfLineMeasure ∧
    (∫ r in Ioi (0:ℝ),
      (affineJapaneseWeight (7/4:ℝ) r*‖R r‖)^2) ≤
        Q*(∫ r in Ioi (0:ℝ), (1+r)^(-(3/2:ℝ))) := by
  dsimp only
  let C : ℝ := actualHartreeBubbleSquaredRieszDecayConstant
  let A0 : ℝ := K^2*C
  let A1 : ℝ := (8*M*K*e)*C
  let AR : ℝ := ((6*M^2+4*M*e+e^2)*e^2)*C
  have hC : 0 ≤ C := by
    dsimp [C]
    exact actualHartreeBubbleSquaredRieszDecayConstant_pos.le
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hA1 : 0 ≤ A1 := by dsimp [A1]; positivity
  have hAR : 0 ≤ AR := by dsimp [AR]; positivity
  have hMeas :=
    actual_Hartree_complex_original_nonlinear_Taylor_measurable
      U H hUmeas hHmeas
  have hRows (r : ℝ) (hr : 0 < r) :=
    actual_Hartree_half_radial_background_and_linear_Riesz_decay
      U H hUmeas hHmeas M K e hM hK he
      hU hHalf hH r hr
  have hQuad (r : ℝ) (hr : 0 < r) :=
    actual_Hartree_quadratic_density_Riesz_spatial_decay_from_Linfty
      U H hUmeas hHmeas M e hM he hU hH r hr
  have h0 (r : ℝ) (hr : 0 < r) :
      IntegrableOn
        (fun x => x*hartreeRadialLog r x*‖U x‖^4) (Ioi (0:ℝ)) :=
    (hRows r hr).1.1
  have h1 (r : ℝ) (hr : 0 < r) :
      IntegrableOn
        (fun x => x*hartreeRadialLog r x*
          actualHartreeComplexDensityLinear (U x) (H x))
        (Ioi (0:ℝ)) :=
    (hRows r hr).2.1
  have hR (r : ℝ) (hr : 0 < r) :
      IntegrableOn
        (fun x => x*hartreeRadialLog r x*
          actualHartreeComplexDensityRemainder (U x) (H x))
        (Ioi (0:ℝ)) :=
    (hQuad r hr).1
  have hP0 (r : ℝ) (hr : 0 < r) :
      (1+r)*|radialHartreePotential (fun x => ‖U x‖^4) r| ≤ A0 := by
    have ht : 0 < 1+r := by linarith
    have h := (le_div_iff₀ ht).1
      (show |radialHartreePotential (fun x => ‖U x‖^4) r| ≤
         A0/(1+r) by simpa only [A0,C] using (hRows r hr).1.2)
    simpa only [mul_comm] using h
  have hP1 (r : ℝ) (hr : 0 < r) :
      (1+r)*|radialHartreePotential
        (fun x => actualHartreeComplexDensityLinear (U x) (H x)) r|
          ≤ A1 := by
    have ht : 0 < 1+r := by linarith
    have h := (le_div_iff₀ ht).1
      (show |radialHartreePotential
        (fun x => actualHartreeComplexDensityLinear (U x) (H x)) r|
        ≤ A1/(1+r) by simpa only [A1,C] using (hRows r hr).2.2)
    simpa only [mul_comm] using h
  have hPR (r : ℝ) (hr : 0 < r) :
      (1+r)*|radialHartreePotential
        (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r|
          ≤ AR := by
    have ht : 0 < 1+r := by linarith
    have h := (le_div_iff₀ ht).1
      (show |radialHartreePotential
        (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r|
        ≤ AR/(1+r) by simpa only [AR,C] using (hQuad r hr).2)
    simpa only [mul_comm] using h
  have hMain :=
    actual_Hartree_full_original_six_term_native_weighted_L2_from_Riesz_rows
      U H hMeas M K e A0 A1 AR hM hK he hA0 hA1 hAR
      hU hHalf hH h0 h1 hR hP0 hP1 hPR
  simpa only [A0,A1,AR,C] using hMain

end HBL.TypeIIDynamicSelection
