import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszSpatialDecay
import HBL.TypeIIDynamicSelection.ActualHartreeMomentSelectedCoreRieszGain
import HBL.TypeIIDynamicSelection.ActualHartreePureRadiationChangedCubicSource
import HBL.TypeIIDynamicSelection.ActualHartreeFullInteractionSourceSplit
import Mathlib.Tactic

/-!
# HBL: one genuine physical radial Hartree radiation slice gives
# a unified nonlocal source normal form with THREE positive length gains

For the SAME real moving monopole V_c, the SAME genuine physical
complex radiation z, its 3D inverse-square quartic physical moment
m[z], and critical spatial scale ell, define
    c=hartreeKappa*ell*m[z],
    Z_ell(r)=sqrt(ell)*z(ell*r).
The original Hartree nonlinearity is I[|u|^4]|u|^2u, where I is the
ACTUAL inverse-square radial logarithmic Riesz convolution.

This is a true multi-component analytical conclusion, not just an
abstract packet constructor: exact four-part Hartree interaction,
pointwise length gains for its core quartic Riesz potential,
pure-radiation quartic Riesz potential, and ALL mixed-quartic Riesz
terms, and a direct bound on pure-radiation potential acting on the
actual CHANGED complex cubic.

A bounded physical quartic moment and physical radial Strauss/L-infty
bounds are explicit, mathematically standard input regularity for one
genuine high-regularity Hartree trajectory. The concentration exponent,
regional PDE profile, Kummer match, moving-cutoff derivative and finite
nonlinear recursive remainder are NOT assumed and remain open.

The result gives strong candidates for revising the old overlarge 2.13
intermediate statement, but DOES NOT claim its original full finite
profile theorem or Type-II blowup orbit without those further steps.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Unified exact nonlocal source estimates from ONE radial Hartree
regular radiation slice. This binds the SAME physical z and quartic
moment to core, mixed, pure, and the four-part interaction source;
the constants are explicit, independent of r and ell. -/
theorem actual_Hartree_one_radiation_full_nonlinear_source_gain
    (ell M B A r : ℝ)
    (hell : 0 < ell)
    (hM : 0 < M)
    (hellMax : ell ≤ min 1 (1 / (hartreeKappa * M)))
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hr : 0 < r)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hm0 : 0 ≤ radialPhysicalQuarticMoment z)
    (hmM : radialPhysicalQuarticMoment z ≤ M)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let c : ℝ := hartreeKappa * ell * radialPhysicalQuarticMoment z
    let V : ℝ → ℝ :=
      monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
    let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
    let Pmix : ℝ := radialHartreePotential
      (actualWholeRadiationMixedQuartic V Z) r
    let Ppure : ℝ := radialHartreePotential
      (fun rho => ‖Z rho‖ ^ 4) r
    let Pcore : ℝ := radialHartreePotential
      (fun rho => V rho ^ 4) r
    |Pcore - 3 * bubble r ^ 2| ≤
      (4 * (hartreeKappa * M) *
          (radialHartreeRowBoundConstant * monopoleRadialBoundConstant) +
        monopoleHartreePotentialBoundConstant *
          (hartreeKappa * M) ^ 2) * ell ∧
    |Ppure| ≤
      (radialHartreeRowBoundConstant *
        (2 * (B ^ 4 + A ^ 4))) * ell ∧
    |Pmix| ≤
      ((4 * (2 + 9 * monopoleRadialBoundConstant) ^ 3 *
          (2 * (B + A)) +
        6 * (2 + 9 * monopoleRadialBoundConstant) ^ 2 *
          (2 * (B + A)) ^ 2 +
        4 * (2 + 9 * monopoleRadialBoundConstant) *
          (2 * (B + A)) ^ 3) *
          actualHartreeBubbleSquaredRieszDecayConstant) *
          Real.sqrt ell / (1 + r) ∧
    ‖(Ppure : ℂ) *
      (actualWholeRadiationLocalCubic
        (fun rho => (V rho : ℂ) + Z rho) r -
        actualWholeRadiationLocalCubic Z r)‖ ≤
      (radialHartreeRowBoundConstant *
        (2 * (B ^ 4 + A ^ 4))) * ell *
      ((‖(V r : ℂ) + Z r‖ + ‖Z r‖) ^ 2 * |V r|) ∧
    actualOneLayerInteractionOnly (fun _ => V) (fun _ => Z) 0 r =
      (Pmix : ℂ) * (V r : ℂ) ^ 3 +
      (Pmix : ℂ) *
        (actualWholeRadiationLocalCubic
          (fun rho => (V rho : ℂ) + Z rho) r -
         actualWholeRadiationLocalCubic
          (fun rho => (V rho : ℂ)) r) +
      (Ppure : ℂ) *
        (actualWholeRadiationLocalCubic
          (fun rho => (V rho : ℂ) + Z rho) r -
         actualWholeRadiationLocalCubic Z r) +
      (Pcore : ℂ) *
        (actualWholeRadiationLocalCubic
          (fun rho => (V rho : ℂ) + Z rho) r -
         actualWholeRadiationLocalCubic
          (fun rho => (V rho : ℂ)) r) := by
  dsimp only
  let m : ℝ := radialPhysicalQuarticMoment z
  let c : ℝ := hartreeKappa * ell * m
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  let Pmix : ℝ := radialHartreePotential
    (actualWholeRadiationMixedQuartic V Z) r
  let Ppure : ℝ := radialHartreePotential
    (fun rho => ‖Z rho‖ ^ 4) r
  let Pcore : ℝ := radialHartreePotential
    (fun rho => V rho ^ 4) r
  have hk : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hK : 0 < hartreeKappa * M := mul_pos hk hM
  have hellOne : ell ≤ 1 := hellMax.trans (min_le_left _ _)
  have hellK : ell ≤ 1 / (hartreeKappa * M) :=
    hellMax.trans (min_le_right _ _)
  have hc0 : 0 ≤ c := by
    dsimp [c,m]
    positivity
  have hc1 : |c| ≤ 1 := by
    have hcM : c ≤ (hartreeKappa * M) * ell := by
      dsimp [c,m]
      have h1 : hartreeKappa * ell * radialPhysicalQuarticMoment z ≤
          hartreeKappa * ell * M :=
        mul_le_mul_of_nonneg_left hmM
          (mul_nonneg hk.le hell.le)
      nlinarith [h1]
    have hEllK : ell * (hartreeKappa * M) ≤ 1 :=
      (le_div_iff₀ hK).mp hellK
    rw [abs_of_nonneg hc0]
    linarith
  have hCore :
      |Pcore - 3 * bubble r ^ 2| ≤
        (4 * (hartreeKappa * M) *
          (radialHartreeRowBoundConstant * monopoleRadialBoundConstant) +
         monopoleHartreePotentialBoundConstant *
          (hartreeKappa * M) ^ 2) * ell := by
    simpa only [Pcore,V,c,m] using
      (actual_Hartree_moment_selected_core_Riesz_length_gain
        ell (radialPhysicalQuarticMoment z) M r
        hell hM hm0 hmM hellMax hr)
  have hPure :
      |Ppure| ≤
        (radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4))) * ell := by
    simpa only [Ppure,Z] using
      (actual_Hartree_pure_radiation_Riesz_uniform_length_gain
        ell r B A hell hr hB hA z hz hSup hStrauss)
  have hMixed :
      |Pmix| ≤
        ((4 * (2 + 9 * monopoleRadialBoundConstant) ^ 3 *
          (2 * (B + A)) +
        6 * (2 + 9 * monopoleRadialBoundConstant) ^ 2 *
          (2 * (B + A)) ^ 2 +
        4 * (2 + 9 * monopoleRadialBoundConstant) *
          (2 * (B + A)) ^ 3) *
          actualHartreeBubbleSquaredRieszDecayConstant) *
          Real.sqrt ell / (1 + r) := by
    simpa only [Pmix,V,Z,c] using
      (actual_Hartree_full_mixed_Riesz_spatial_decay
        ell c r B A hell hellOne hr hc1
        hB hA z hz hSup hStrauss)
  have hPureCubic :
      ‖(Ppure : ℂ) *
        (actualWholeRadiationLocalCubic
          (fun rho => (V rho : ℂ) + Z rho) r -
          actualWholeRadiationLocalCubic Z r)‖ ≤
        (radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4))) * ell *
        ((‖(V r : ℂ) + Z r‖ + ‖Z r‖) ^ 2 * |V r|) := by
    simpa only [Ppure,V,Z,c] using
      (actual_Hartree_pure_radiation_changed_cubic_source_gain
        ell c r B A hell hr hB hA z hz hSup hStrauss)
  have hSplit :
      actualOneLayerInteractionOnly
          (fun _ : ℝ => V) (fun _ : ℝ => Z) 0 r =
        (Pmix : ℂ) * (V r : ℂ) ^ 3 +
        (Pmix : ℂ) *
          (actualWholeRadiationLocalCubic
            (fun rho => (V rho : ℂ) + Z rho) r -
            actualWholeRadiationLocalCubic
              (fun rho => (V rho : ℂ)) r) +
        (Ppure : ℂ) *
          (actualWholeRadiationLocalCubic
            (fun rho => (V rho : ℂ) + Z rho) r -
            actualWholeRadiationLocalCubic Z r) +
        (Pcore : ℂ) *
          (actualWholeRadiationLocalCubic
            (fun rho => (V rho : ℂ) + Z rho) r -
            actualWholeRadiationLocalCubic
              (fun rho => (V rho : ℂ)) r) := by
    have hRealQuartic :
        (fun rho : ℝ => ‖(V rho : ℂ)‖ ^ 4) =
          (fun rho : ℝ => V rho ^ 4) := by
      funext rho
      rw [Complex.norm_real]
      calc
        |V rho| ^ 4 = (|V rho| ^ 2) ^ 2 := by ring
        _ = (V rho ^ 2) ^ 2 := by rw [sq_abs]
        _ = V rho ^ 4 := by ring
    have hCorePotential :
        radialHartreePotential (fun rho : ℝ => ‖(V rho : ℂ)‖ ^ 4) r =
          Pcore := by
      change radialHartreePotential (fun rho : ℝ => ‖(V rho : ℂ)‖ ^ 4) r =
        radialHartreePotential (fun rho : ℝ => V rho ^ 4) r
      rw [hRealQuartic]
    simpa only [Pmix,Ppure,Pcore,hRealQuartic] using
      (actual_Hartree_complete_nonlinear_interaction_four_term_split
        (fun _ : ℝ => V) (fun _ : ℝ => Z) 0 r)
  exact ⟨hCore, hPure, hMixed, hPureCubic, hSplit⟩

end HBL.TypeIIDynamicSelection
