import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszEnvelope
import HBL.WeightedPhaseAffineSource
import Mathlib.Tactic

/-!
# Revised HBL 2.13: genuine mixed Hartree Riesz potential times physical cubic

This module moves from the true whole mixed inverse-square Hartree
density to the weighted local *source entering the actual cubic factor*.

The genuine monopole is V_c(r)=W(r)+c(1-cutoff(|c|r/4))Phi(r).
The previous strictly constructed radial estimates imply
  |V_c(r)| <= D/(1+r)
uniformly in the physical moment coefficient |c|<=1.
For 0<=sigma<=2 the original Fredholm weight obeys
  <r>^sigma |V_c(r)|^3 <= D^3 W(r).

Composing this radial inequality with the true full nonlocal Riesz
bound of the exact quartic mixed density yields a pointwise
weighted source envelope C*sqrt(ell)*W(r).

No local cubic replacement, assumed time-decay exponent, or artificial
generated-source order appears. A later theorem must establish full
weighted L2 membership and join this term to the actual same-PDE
inner/Kummer/remote cancellation. Revised original 2.13 remains OPEN.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Explicit weighted spatial integrability factor for the true
moment-cutoff monopole cubic. It is the original Fredholm weight,
not a bespoke source-order norm. -/
theorem actual_Hartree_weighted_moving_monopole_cubic_bubble_bound
    (c r sigma : ℝ) (hr : 0 < r)
    (hc : |c| ≤ 1) (hSigma : sigma ≤ 2) :
    affineJapaneseWeight sigma r *
      |monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c r| ^ 3 ≤
      (2 + 9 * monopoleRadialBoundConstant) ^ 3 * bubble r := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  have hD : 0 ≤ D := by
    dsimp [D]
    have hmon := monopoleRadialBoundConstant_pos
    positivity
  have hrad : (1 + r) * |V r| ≤ D := by
    simpa only [V, D] using
      actual_Hartree_moving_monopole_one_plus_radius_decay c r hr hc
  have hpos : 0 < 1 + r := by linarith
  have hVdiv : |V r| ≤ D / (1 + r) := by
    apply (le_div_iff₀ hpos).2
    calc
      |V r| * (1 + r) = (1 + r) * |V r| := by ring
      _ ≤ D := hrad
  have hgeom : 1 + r ^ 2 ≤ (1 + r) ^ 2 := by
    nlinarith [hr.le]
  have hsqrt : Real.sqrt (1 + r ^ 2) ≤ 1 + r := by
    calc
      _ ≤ Real.sqrt ((1 + r) ^ 2) := Real.sqrt_le_sqrt hgeom
      _ = 1 + r := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hpos]
  have hBge : (1 + r)⁻¹ ≤ bubble r := by
    have hp : 0 < Real.sqrt (1 + r ^ 2) :=
      Real.sqrt_pos.mpr (by positivity)
    have hi := one_div_le_one_div_of_le hp hsqrt
    simpa only [one_div, bubble] using hi
  have hVb : |V r| ≤ D * bubble r := by
    calc
      |V r| ≤ D / (1 + r) := hVdiv
      _ = D * (1 + r)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ D * bubble r := mul_le_mul_of_nonneg_left hBge hD
  have hV3 : |V r| ^ 3 ≤ D ^ 3 * bubble r ^ 3 := by
    calc
      _ ≤ (D * bubble r) ^ 3 :=
        pow_le_pow_left₀ (abs_nonneg _) hVb 3
      _ = D ^ 3 * bubble r ^ 3 := by ring
  have hw : affineJapaneseWeight sigma r ≤ 1 + r ^ 2 :=
    affineJapaneseWeight_le_one_add_sq sigma r hSigma
  have hw0 : 0 ≤ affineJapaneseWeight sigma r := by
    unfold affineJapaneseWeight
    positivity
  have hb0 : 0 ≤ bubble r := by
    unfold bubble
    positivity
  have hb2 : bubble r ^ 2 = (1 + r ^ 2)⁻¹ := by
    unfold bubble
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  have hWb : affineJapaneseWeight sigma r * bubble r ^ 3 ≤
      bubble r := by
    calc
      _ ≤ (1 + r ^ 2) * bubble r ^ 3 :=
        mul_le_mul_of_nonneg_right hw (by positivity)
      _ = ((1 + r ^ 2) * bubble r ^ 2) * bubble r := by ring
      _ = bubble r := by
        rw [hb2]
        field_simp [show 1 + r ^ 2 ≠ 0 by positivity]
  change affineJapaneseWeight sigma r * |V r| ^ 3 ≤
    D ^ 3 * bubble r
  calc
    _ ≤ affineJapaneseWeight sigma r * (D ^ 3 * bubble r ^ 3) :=
      mul_le_mul_of_nonneg_left hV3 hw0
    _ = D ^ 3 * (affineJapaneseWeight sigma r * bubble r ^ 3) := by
      ring
    _ ≤ D ^ 3 * bubble r :=
      mul_le_mul_of_nonneg_left hWb (by positivity)

/-- The entire genuine mixed-quartic Hartree nonlocal Riesz potential
multiplied by the ACTUAL moving-monopole cubic, in the manuscript
weighted source variable, has positive half-order scale gain.
Every real-linear, quadratic and cubic cross interaction is retained. -/
theorem actual_Hartree_full_mixed_Riesz_times_monopole_cubic_weighted_pointwise
    (ell c r B A sigma : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hr : 0 < r)
    (hc : |c| ≤ 1) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hSigma : sigma ≤ 2)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    affineJapaneseWeight sigma r *
      ‖(radialHartreePotential
        (actualWholeRadiationMixedQuartic
          (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c)
          (rescalePhysicalRadiation ell z)) r : ℂ) *
        ((monopolePerturbedRadialProfile
          (monopoleQuadraticRadius c) c r : ℂ) ^ 3)‖ ≤
      ((radialHartreeRowBoundConstant *
        (4 * (2 + 9 * monopoleRadialBoundConstant) ^ 3 *
          (2 * (B + A)) +
         6 * (2 + 9 * monopoleRadialBoundConstant) ^ 2 *
          (2 * (B + A)) ^ 2 +
         4 * (2 + 9 * monopoleRadialBoundConstant) *
          (2 * (B + A)) ^ 3)) *
        (2 + 9 * monopoleRadialBoundConstant) ^ 3) *
          Real.sqrt ell * bubble r := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let F : ℝ → ℝ :=
    actualWholeRadiationMixedQuartic V (rescalePhysicalRadiation ell z)
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let C : ℝ :=
    radialHartreeRowBoundConstant *
      (4 * D ^ 3 * (2 * (B + A)) +
       6 * D ^ 2 * (2 * (B + A)) ^ 2 +
       4 * D * (2 * (B + A)) ^ 3)
  let P : ℝ := radialHartreePotential F r
  have hC : 0 ≤ C := by
    dsimp [C, D]
    have hmon := monopoleRadialBoundConstant_pos
    have hrow := radialHartreeRowBoundConstant_pos
    positivity
  have hPotential : |P| ≤ C * Real.sqrt ell := by
    have h :=
      (actual_Hartree_full_mixed_nonlinear_Riesz_from_Strauss
        ell c r B A hell hellOne hr hc hB hA
        z hz hSup hStrauss).2
    simpa only [P, F, V, C, D, mul_assoc] using h
  have hWeight : affineJapaneseWeight sigma r * |V r| ^ 3 ≤
      D ^ 3 * bubble r := by
    simpa only [D, V] using
      actual_Hartree_weighted_moving_monopole_cubic_bubble_bound
        c r sigma hr hc hSigma
  have hNorm :
      ‖(P : ℂ) * ((V r : ℂ) ^ 3)‖ = |P| * |V r| ^ 3 := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  change affineJapaneseWeight sigma r *
    ‖(P : ℂ) * ((V r : ℂ) ^ 3)‖ ≤
    (C * D ^ 3) * Real.sqrt ell * bubble r
  rw [hNorm]
  calc
    affineJapaneseWeight sigma r * (|P| * |V r| ^ 3) =
      |P| * (affineJapaneseWeight sigma r * |V r| ^ 3) := by ring
    _ ≤ (C * Real.sqrt ell) * (D ^ 3 * bubble r) := by
      have hWeightedNonneg :
          0 ≤ affineJapaneseWeight sigma r * |V r| ^ 3 := by
        unfold affineJapaneseWeight
        positivity
      have hScaledNonneg : 0 ≤ C * Real.sqrt ell :=
        mul_nonneg hC (Real.sqrt_nonneg ell)
      exact mul_le_mul hPotential hWeight hWeightedNonneg hScaledNonneg
    _ = (C * D ^ 3) * Real.sqrt ell * bubble r := by ring

end HBL.TypeIIDynamicSelection
