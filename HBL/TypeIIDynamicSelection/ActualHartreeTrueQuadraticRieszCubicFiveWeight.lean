import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceQuadraticRieszSpatialDecay
import HBL.TypeIIDynamicSelection.ActualHartreeScaledRadiationHalfPower
import HBL.TypeIIDynamicSelection.ActualHartreeComplexCubicLipschitz
import Mathlib.Tactic

/-!
# True two-scale Hartree quadratic Riesz density times the original cubic

These are the genuine nonlocal radial inverse-square Riesz convolution and
the genuine complex cubic factor on one physical V_c + sqrt(ell) z(ell*r)
background. In particular the radiation is NOT given a false ell-uniform
single-bubble envelope. The fifth polynomial weight is exactly the
squared source decay sufficient for the original L^(2,7/4) norm.

These source terms are a subset of the full nonlinear Taylor remainder.
No moving physical PDE cancellation or full positive-order time estimate
is assumed or claimed here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Real physical two-scale profile has exactly the uniform HALF-radial
squared amplitude, not the false uniform bubble amplitude. -/
theorem actual_Hartree_true_two_scale_background_half_radial_square
    (ell c r B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hr : 0 < r) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let U : ℂ :=
      (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r : ℂ) +
        rescalePhysicalRadiation ell z r
    (1 + r) * ‖U‖ ^ 2 ≤
      2 * ((2 + 9 * monopoleRadialBoundConstant) ^ 2 +
        (2 * (B + A)) ^ 2) := by
  dsimp only
  let V : ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r
  let Z : ℂ := rescalePhysicalRadiation ell z r
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let E : ℝ := 2 * (B + A)
  have hD : 0 ≤ D := by
    dsimp [D]
    have := monopoleRadialBoundConstant_pos
    positivity
  have hw : 0 ≤ 1 + r := by linarith
  have hwOne : 1 ≤ 1 + r := by linarith
  have hV : (1 + r) * ‖(V : ℂ)‖ ≤ D := by
    simpa only [V, D, Complex.norm_real, Real.norm_eq_abs] using
      actual_Hartree_moving_monopole_one_plus_radius_decay c r hr hc
  have hVBound : ‖(V : ℂ)‖ ≤ D := by
    have hfirst : 1 * ‖(V : ℂ)‖ ≤ (1 + r) * ‖(V : ℂ)‖ :=
      mul_le_mul_of_nonneg_right hwOne (norm_nonneg _)
    simpa only [one_mul] using hfirst.trans hV
  have hVSq : (1 + r) * ‖(V : ℂ)‖ ^ 2 ≤ D ^ 2 := by
    calc
      _ = ((1 + r) * ‖(V : ℂ)‖) * ‖(V : ℂ)‖ := by ring
      _ ≤ D * D := mul_le_mul hV hVBound (norm_nonneg _) hD
      _ = D ^ 2 := by ring
  have hZSq : (1 + r) * ‖Z‖ ^ 2 ≤ E ^ 2 := by
    simpa only [Z, E] using
      actual_Hartree_scaled_radiation_halfpower_squared
        ell r B A hell hellOne hr hB hA z hSup hStrauss
  have hSum : ‖(V : ℂ) + Z‖ ≤ ‖(V : ℂ)‖ + ‖Z‖ :=
    norm_add_le _ _
  have hPow := pow_le_pow_left₀ (norm_nonneg ((V : ℂ) + Z)) hSum 2
  have hSq : ‖(V : ℂ) + Z‖ ^ 2 ≤
      2 * (‖(V : ℂ)‖ ^ 2 + ‖Z‖ ^ 2) := by
    nlinarith only [hPow, sq_nonneg (‖(V : ℂ)‖ - ‖Z‖)]
  calc
    (1 + r) * ‖(V : ℂ) + Z‖ ^ 2 ≤
        (1 + r) * (2 * (‖(V : ℂ)‖ ^ 2 + ‖Z‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hSq hw
    _ = 2 * ((1 + r) * ‖(V : ℂ)‖ ^ 2 +
        (1 + r) * ‖Z‖ ^ 2) := by ring
    _ ≤ 2 * (D ^ 2 + E ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hVSq hZSq) (by norm_num)
    _ = 2 * ((2 + 9 * monopoleRadialBoundConstant) ^ 2 +
        (2 * (B + A)) ^ 2) := rfl

/-- A Riesz potential of order (1+r)^(-1), multiplied by the true
complex cubic of a HALF-radial background, has squared fifth-weight
control. This is the polynomial form of the integrable
(1+r)^(-3/2) weighted-L2-square tail. -/
theorem actual_Hartree_density_Riesz_cubic_fifth_weight_from_true_budgets
    (U H : ℝ → ℂ) (r : ℝ) (hr : 0 < r) (P K : ℝ)
    (hPotential :
      |radialHartreePotential
        (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r| ≤
          P / (1 + r))
    (hHalf : (1 + r) * ‖U r‖ ^ 2 ≤ K) :
    (1 + r) ^ 5 *
      ‖(radialHartreePotential
          (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r : ℂ) *
        actualHartreeComplexCubic (U r)‖ ^ 2 ≤
      P ^ 2 * K ^ 3 := by
  let q : ℝ :=
    radialHartreePotential
      (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r
  have hw : 0 < 1 + r := by linarith
  have hP : (1 + r) * |q| ≤ P := by
    have h := (le_div_iff₀ hw).mp hPotential
    simpa only [q, mul_comm] using h
  have hP2 : ((1 + r) * |q|) ^ 2 ≤ P ^ 2 :=
    pow_le_pow_left₀ (by positivity) hP 2
  have hK3 : ((1 + r) * ‖U r‖ ^ 2) ^ 3 ≤ K ^ 3 :=
    pow_le_pow_left₀ (by positivity) hHalf 3
  have hProd :
      ((1 + r) * |q|) ^ 2 *
        ((1 + r) * ‖U r‖ ^ 2) ^ 3 ≤
      P ^ 2 * K ^ 3 :=
    mul_le_mul hP2 hK3 (by positivity) (sq_nonneg P)
  have hNorm :
      ‖(q : ℂ) * actualHartreeComplexCubic (U r)‖ =
      |q| * ‖U r‖ ^ 3 := by
    unfold actualHartreeComplexCubic
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖U r‖)]
    ring
  change (1 + r) ^ 5 *
      ‖(q : ℂ) * actualHartreeComplexCubic (U r)‖ ^ 2 ≤
    P ^ 2 * K ^ 3
  calc
    _ = ((1 + r) * |q|) ^ 2 *
          ((1 + r) * ‖U r‖ ^ 2) ^ 3 := by
      rw [hNorm]
      ring
    _ ≤ P ^ 2 * K ^ 3 := hProd

/-- No synthetic forcing packet or uniform single-bubble physical
background is inserted. Every nonlocal density, cubic and physical
scale belongs to the SAME actual V_c + Z_ell field. -/
theorem actual_Hartree_true_two_scale_quadratic_Riesz_cubic_fifth_weight
    (ell c B A e : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hc : |c| ≤ 1) (hB : 0 ≤ B) (hA : 0 ≤ A) (he : 0 ≤ e)
    (z H : ℝ → ℂ)
    (hz : Measurable z) (hHmeas : Measurable H)
    (hSup : ∀ x : ℝ, 0 < x → ‖z x‖ ≤ B)
    (hStrauss : ∀ x : ℝ, 1 ≤ x → x * ‖z x‖ ≤ A)
    (hHB : ∀ x : ℝ, 0 < x → ‖H x‖ ≤ e * bubble x)
    (r : ℝ) (hr : 0 < r) :
    let U : ℝ → ℂ := fun x =>
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c x : ℂ) +
          rescalePhysicalRadiation ell z x
    let M : ℝ := 1 + monopoleRadialBoundConstant + B
    let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
    let E : ℝ := 2 * (B + A)
    let P : ℝ := ((6 * M ^ 2 + 4 * M * e + e ^ 2) * e ^ 2) *
      actualHartreeBubbleSquaredRieszDecayConstant
    let K : ℝ := 2 * (D ^ 2 + E ^ 2)
    (1 + r) ^ 5 *
      ‖(radialHartreePotential
          (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r : ℂ) *
        actualHartreeComplexCubic (U r)‖ ^ 2 ≤
      P ^ 2 * K ^ 3 := by
  dsimp only
  let U : ℝ → ℂ := fun x =>
    (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius c) c x : ℂ) +
        rescalePhysicalRadiation ell z x
  let M : ℝ := 1 + monopoleRadialBoundConstant + B
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let E : ℝ := 2 * (B + A)
  let P : ℝ := ((6 * M ^ 2 + 4 * M * e + e ^ 2) * e ^ 2) *
    actualHartreeBubbleSquaredRieszDecayConstant
  let K : ℝ := 2 * (D ^ 2 + E ^ 2)
  have hSource :=
    (actual_Hartree_true_monopole_radiation_quadratic_density_Riesz_spatial_decay
      ell c B e hell hellOne hc hB he z H hz hHmeas hSup hHB r hr).2
  have hPotential :
      |radialHartreePotential
        (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r| ≤
          P / (1 + r) := by
    simpa only [P, M, U] using hSource
  have hHalf : (1 + r) * ‖U r‖ ^ 2 ≤ K := by
    simpa only [K, D, E, U] using
      actual_Hartree_true_two_scale_background_half_radial_square
        ell c r B A hell hellOne hr hc hB hA z hSup hStrauss
  exact actual_Hartree_density_Riesz_cubic_fifth_weight_from_true_budgets
    U H r hr P K hPotential hHalf

end HBL.TypeIIDynamicSelection
