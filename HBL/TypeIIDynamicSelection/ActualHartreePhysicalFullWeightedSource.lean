import HBL.TypeIIDynamicSelection.ActualHartreeTenMonomialWeightedGain
import HBL.TypeIIDynamicSelection.ActualHartreeCoreRieszSpatialDecay
import HBL.TypeIIDynamicSelection.ActualHartreePureRadiationRieszSpatialDecay
import Mathlib.Tactic

/-!
# Complete actual Hartree interaction: uniform physical weighted source estimate

The nonlocal source is the original interaction of the moving cutoff
monopole and the critically rescaled radiation. All three Riesz bounds
and both field envelopes are DERIVED from their existing original-kernel
lemmas. No potential bound or weighted source estimate is an additional
hypothesis. The explicit constant depends only on the physical amplitude
and Strauss bounds B,A, not on ell,c,r or a concentration-time exponent.

This source estimate does not assert a matched three-region correction,
a positive time-order recursion, or the Type-II blowup theorem.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- One original Hartree interaction, with its actual moving core and
critical radiation scaling, as a function of observation radius. -/
def actualHartreePhysicalSliceInteraction
    (ell c : ℝ) (z : ℝ → ℂ) : ℝ → ℂ :=
  actualOneLayerInteractionOnly
    (fun _ : ℝ => monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c)
    (fun _ : ℝ => rescalePhysicalRadiation ell z) 0

/-- Uniform constant: no scale, radius, source, or blowup rate dependence. -/
def actualHartreePhysicalWeightedSourceConstant (B A : ℝ) : ℝ :=
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let E : ℝ := 2 * (B + A)
  let CW : ℝ := actualHartreeBubbleSquaredRieszDecayConstant
  actualHartreeTenTermSourceConstant D E
    ((4 * D ^ 3 * E + 6 * D ^ 2 * E ^ 2 + 4 * D * E ^ 3) * CW)
    (2 * (B ^ 4 + A ^ 4) * CW) (D ^ 4 * CW)

theorem actualHartreePhysicalWeightedSourceConstant_nonneg
    (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    0 ≤ actualHartreePhysicalWeightedSourceConstant B A := by
  have hMon := monopoleRadialBoundConstant_pos
  have hCW := actualHartreeBubbleSquaredRieszDecayConstant_pos
  dsimp [actualHartreePhysicalWeightedSourceConstant,
    actualHartreeTenTermSourceConstant]
  positivity

/-- The full original nonlocal Hartree interaction has the critical
weighted epsilon=1/8 envelope. Only measurability and physical radial
amplitude/Strauss input remain; all Riesz/source bounds are conclusions. -/
theorem actual_Hartree_physical_full_interaction_weighted_pointwise
    (ell c r B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hr : 0 < r) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    (1 + r) ^ (7 / 4 : ℝ) *
      ‖actualHartreePhysicalSliceInteraction ell c z r‖ ≤
    actualHartreePhysicalWeightedSourceConstant B A *
      ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let E : ℝ := 2 * (B + A)
  let CW : ℝ := actualHartreeBubbleSquaredRieszDecayConstant
  let Cm : ℝ := (4 * D ^ 3 * E + 6 * D ^ 2 * E ^ 2 + 4 * D * E ^ 3) * CW
  let Cz : ℝ := 2 * (B ^ 4 + A ^ 4) * CW
  let Cc : ℝ := D ^ 4 * CW
  let pm : ℝ := radialHartreePotential (actualWholeRadiationMixedQuartic V Z) r
  let pz : ℝ := radialHartreePotential (fun rho => ‖Z rho‖ ^ 4) r
  let pc : ℝ := radialHartreePotential (fun rho => ‖(V rho : ℂ)‖ ^ 4) r
  have hD : 0 ≤ D := by
    dsimp [D]
    have hMon := monopoleRadialBoundConstant_pos
    positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hCW : 0 ≤ CW := actualHartreeBubbleSquaredRieszDecayConstant_pos.le
  have hCm : 0 ≤ Cm := by dsimp [Cm]; positivity
  have hCz : 0 ≤ Cz := by dsimp [Cz]; positivity
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hd : 0 < 1 + r := by linarith
  have hq : 0 < 1 + ell * r := by positivity
  have hVraw : (1 + r) * |V r| ≤ D :=
    actual_Hartree_moving_monopole_one_plus_radius_decay c r hr hc
  have hVabs : |V r| ≤ D / (1 + r) :=
    (le_div_iff₀ hd).2 (by simpa only [mul_comm] using hVraw)
  have hV : ‖(V r : ℂ)‖ ≤ D / (1 + r) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hVabs
  have hZraw : (1 + ell * r) * ‖Z r‖ ≤ E * Real.sqrt ell :=
    actual_Hartree_scaled_Strauss_global_radial_decay
      ell r B A hell hr hB hA z hSup hStrauss
  have hZ : ‖Z r‖ ≤ E * Real.sqrt ell / (1 + ell * r) :=
    (le_div_iff₀ hq).2 (by simpa only [mul_comm] using hZraw)
  have hPm : |pm| ≤ Cm * Real.sqrt ell / (1 + r) :=
    actual_Hartree_full_mixed_Riesz_spatial_decay
      ell c r B A hell hellOne hr hc hB hA z hz hSup hStrauss
  have hPz : |pz| ≤ Cz * ell / (1 + ell * r) :=
    actual_Hartree_pure_radiation_Riesz_global_scaled_decay
      ell r B A hell hr hB hA z hz hSup hStrauss
  have hRealQuartic :
      (fun rho : ℝ => ‖(V rho : ℂ)‖ ^ 4) =
        (fun rho : ℝ => V rho ^ 4) := by
    funext rho
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      |V rho| ^ 4 = (|V rho| ^ 2) ^ 2 := by ring
      _ = (V rho ^ 2) ^ 2 := by rw [sq_abs]
      _ = V rho ^ 4 := by ring
  have hPc : |pc| ≤ Cc / (1 + r) := by
    dsimp only [pc]
    rw [hRealQuartic]
    exact actual_Hartree_moving_core_Riesz_global_inverse_radius c r hc hr
  have hScalar :=
    actual_Hartree_all_ten_monomials_weighted_one_eighth_gain
      ell r D E Cm Cz Cc |pm| |pz| |pc| ‖(V r : ℂ)‖ ‖Z r‖
      hell hellOne hr.le hD hE hCm hCz hCc
      (abs_nonneg pm) (abs_nonneg pz) (abs_nonneg pc)
      (norm_nonneg _) (norm_nonneg _) hPm hPz hPc hV hZ
  change (1 + r) ^ (7 / 4 : ℝ) *
      actualHartreePhysicalInteractionTenTermEnvelope
        (fun _ : ℝ => V) (fun _ : ℝ => Z) 0 r ≤
    actualHartreePhysicalWeightedSourceConstant B A *
      ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) at hScalar
  have hNorm := actual_Hartree_physical_interaction_complete_ten_term_norm_le
    (fun _ : ℝ => V) (fun _ : ℝ => Z) 0 r
  have hWeighted := mul_le_mul_of_nonneg_left hNorm
    (Real.rpow_nonneg hd.le (7 / 4 : ℝ))
  exact hWeighted.trans hScalar

/-- Original Japanese Fredholm weight is no larger than the radial
weight already controlled for the complete actual physical source. -/
theorem actual_Hartree_physical_full_interaction_Japanese_pointwise
    (ell c r B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hr : 0 < r) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    affineJapaneseWeight (7 / 4 : ℝ) r *
      ‖actualHartreePhysicalSliceInteraction ell c z r‖ ≤
    actualHartreePhysicalWeightedSourceConstant B A *
      ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) := by
  have hd : 0 < 1 + r := by linarith
  have hGeom : 1 + r ^ 2 ≤ (1 + r) ^ 2 := by nlinarith [hr.le]
  have hPow := Real.rpow_le_rpow
    (by positivity : 0 ≤ 1 + r ^ 2) hGeom
    (show (0 : ℝ) ≤ 7 / 8 by norm_num)
  have hRight : ((1 + r) ^ 2) ^ (7 / 8 : ℝ) =
      (1 + r) ^ (7 / 4 : ℝ) := by
    calc
      _ = ((1 + r) ^ (2 : ℝ)) ^ (7 / 8 : ℝ) := by
        rw [Real.rpow_natCast]
      _ = (1 + r) ^ ((2 : ℝ) * (7 / 8 : ℝ)) :=
        (Real.rpow_mul hd.le 2 (7 / 8)).symm
      _ = _ := by norm_num
  have hWeight : affineJapaneseWeight (7 / 4 : ℝ) r ≤
      (1 + r) ^ (7 / 4 : ℝ) := by
    change (1 + r ^ 2) ^ ((7 / 4 : ℝ) / 2) ≤ (1 + r) ^ (7 / 4 : ℝ)
    convert hPow.trans_eq hRight using 1; norm_num
  exact (mul_le_mul_of_nonneg_right hWeight (norm_nonneg _)).trans
    (actual_Hartree_physical_full_interaction_weighted_pointwise
      ell c r B A hell hellOne hc hr hB hA z hz hSup hStrauss)

end HBL.TypeIIDynamicSelection
