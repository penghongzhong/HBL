import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeMixedL1
import HBL.TypeIIDynamicSelection.ExteriorSpatialGain
import Mathlib.Tactic

/-!
# Actual TOTAL nonlinear mixed quartic Hartree Riesz core

This is the complete physical mixed density
  |V_c+Z_ell|^4-|V_c|^4-|Z_ell|^4
including the real-linear, quadratic and cubic cross terms, not
only the previously certified real-linear approximation.

For the fixed nonzero annular terminal radiation, the original
half-line Hartree-Riesz operator equals the genuine exterior Riesz
operator with NO introduced remote-source hypothesis. The exact
full physical centre is its exterior threshold charge.

The already derived full quartic L1 envelope and original
inverse-square Hartree multipole estimate yield
  |I(F)(r)-Center(F)| <= 64*pi*kappa_H*r²*ell²*Envelope(ell)
on 0<2r<=1/(4ell). Since Envelope(ell)=O(ell^(3/2)),
this is an O(r² ell^(7/2)) core defect.

This remains terminal-time source matching, not full 2.12 closure.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

private theorem actual_one_orbit_Vc_whole_mixed_zero_below
    (ell : ℝ) (hell : 0 < ell) {r : ℝ}
    (hr : r ≤ 1 / (4 * ell)) :
    actualOneOrbitVcWholeMixedQuartic ell r = 0 := by
  have hz := actual_one_orbit_rescaled_terminal_zero_core ell r hell hr
  simp [actualOneOrbitVcWholeMixedQuartic,
    actualWholeRadiationMixedQuartic, hz]

/-- The original entire mixed Hartree source equals its physical
exterior indicator, not a model-local-cubic replacement. -/
theorem actual_one_orbit_Vc_whole_mixed_exterior_indicator
    (ell : ℝ) (hell : 0 < ell) :
    (Ioi (1 / (4 * ell))).indicator
      (actualOneOrbitVcWholeMixedQuartic ell) =
      actualOneOrbitVcWholeMixedQuartic ell := by
  funext rho
  by_cases h : 1 / (4 * ell) < rho
  · simp [Set.indicator, h]
  · have hz := actual_one_orbit_Vc_whole_mixed_zero_below
      ell hell (r := rho) (le_of_not_gt h)
    simp [Set.indicator, h, hz]

/-- Total mixed Hartree monopole charge is identically the exterior
charge of the exact same nonlinear quartic-density source. -/
theorem actual_one_orbit_Vc_whole_mixed_center_eq_exterior
    (ell : ℝ) (hell : 0 < ell) :
    radialHartreeCenter (actualOneOrbitVcWholeMixedQuartic ell) =
      radialHartreeExteriorCenter
        (actualOneOrbitVcWholeMixedQuartic ell) (1 / (4 * ell)) := by
  let F : ℝ → ℝ := actualOneOrbitVcWholeMixedQuartic ell
  let a : ℝ := 1 / (4 * ell)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : Ioi a ⊆ Ioi (0 : ℝ) :=
    fun r hr => ha.trans_lt hr
  have hMask : (Ioi a).indicator F = F := by
    simpa only [F, a] using
      actual_one_orbit_Vc_whole_mixed_exterior_indicator ell hell
  have hIntegral :
      (∫ rho in Ioi (0 : ℝ), F rho) =
        ∫ rho in Ioi a, F rho := by
    calc
      _ = ∫ rho in Ioi (0 : ℝ), (Ioi a).indicator F rho := by
        rw [hMask]
      _ = ∫ rho in Ioi (0 : ℝ) ∩ Ioi a, F rho :=
        setIntegral_indicator measurableSet_Ioi
      _ = ∫ rho in Ioi a, F rho := by rw [inter_eq_right.mpr hs]
  unfold radialHartreeCenter radialHartreeExteriorCenter
  rw [hIntegral]

/-- The true radial inverse-square Hartree Riesz integral of the
complete mixed quartic density equals the physical exterior integral. -/
theorem actual_one_orbit_Vc_whole_mixed_Riesz_eq_exterior
    (ell r : ℝ) (hell : 0 < ell) :
    radialHartreePotential (actualOneOrbitVcWholeMixedQuartic ell) r =
      radialHartreeExteriorPotential
        (actualOneOrbitVcWholeMixedQuartic ell) (1 / (4 * ell)) r := by
  have hMask :=
    actual_one_orbit_Vc_whole_mixed_exterior_indicator ell hell
  rw [radialHartreeExteriorPotential_eq_indicator
    (actualOneOrbitVcWholeMixedQuartic ell)
    (by positivity : 0 ≤ 1 / (4 * ell)) r]
  rw [hMask]

/-- Positive spatial gain for the COMPLETE physical mixed quartic
Hartree source, including absolute convergence of the original full
Riesz row. This is the true source used by the 2.12 regional solver. -/
theorem actual_one_orbit_Vc_whole_mixed_Riesz_core_gain
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (hsep : 2 * r ≤ 1 / (4 * ell)) :
    IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualOneOrbitVcWholeMixedQuartic ell rho)
      (Ioi (0 : ℝ)) ∧
    |radialHartreePotential (actualOneOrbitVcWholeMixedQuartic ell) r -
        radialHartreeCenter (actualOneOrbitVcWholeMixedQuartic ell)| ≤
      64 * Real.pi * hartreeKappa * r ^ 2 * ell ^ 2 *
        actualOneOrbitVcWholeMixedL1Envelope ell := by
  let F : ℝ → ℝ := actualOneOrbitVcWholeMixedQuartic ell
  let a : ℝ := 1 / (4 * ell)
  have ha : 0 < a := by dsimp [a]; positivity
  have hFmeas : Measurable F :=
    actual_one_orbit_Vc_whole_mixed_measurable ell
  have hSource :=
    actual_one_orbit_Vc_whole_mixed_Hartree_L1_center_gain ell hell
  have hFext : IntegrableOn F (Ioi a) :=
    hSource.1.integrableOn.mono_set (fun x hx => ha.trans hx)
  have hsep' : 2 * r ≤ a := hsep
  obtain ⟨_hWeighted, hRow, _hError⟩ :=
    radialHartreeExteriorPotential_quadratic_center
      F hFmeas hFext ha hr hsep'
  let G : ℝ → ℝ :=
    fun rho => rho * hartreeRadialLog r rho * F rho
  have hNear : IntegrableOn G (Ioc (0 : ℝ) a) := by
    apply integrableOn_zero.congr_fun ?_ measurableSet_Ioc
    intro rho hρ
    have hz := actual_one_orbit_Vc_whole_mixed_zero_below
      ell hell (r := rho) hρ.2
    simp [G, F, hz]
  have hFull : IntegrableOn G (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact hNear.union hRow
  have hs : Ioi a ⊆ Ioi (0 : ℝ) :=
    fun x hx => ha.trans_lt hx
  have hAbsMask :
      (Ioi a).indicator (fun rho => |F rho|) =
        (fun rho => |F rho|) := by
    funext rho
    by_cases h : a < rho
    · simp [Set.indicator, h]
    · have hz := actual_one_orbit_Vc_whole_mixed_zero_below
        ell hell (r := rho) (le_of_not_gt h)
      simp [Set.indicator, h, F, hz]
  have hAbsEq :
      (∫ rho in Ioi a, |F rho|) =
        ∫ rho in Ioi (0 : ℝ), |F rho| := by
    calc
      _ = ∫ rho in Ioi (0 : ℝ) ∩ Ioi a, |F rho| := by
        rw [inter_eq_right.mpr hs]
      _ = ∫ rho in Ioi (0 : ℝ),
            (Ioi a).indicator (fun rho => |F rho|) rho :=
        (setIntegral_indicator measurableSet_Ioi).symm
      _ = ∫ rho in Ioi (0 : ℝ), |F rho| := by rw [hAbsMask]
  have hL1 :
      (∫ rho in Ioi a, |F rho|) ≤
        actualOneOrbitVcWholeMixedL1Envelope ell := by
    rw [hAbsEq]
    exact hSource.2.1
  have hκ : 0 ≤
      4 * Real.pi * hartreeKappa * r ^ 2 * (1 / a ^ 2) := by
    unfold hartreeKappa
    positivity
  have hGap :
      |radialHartreePotential F r - radialHartreeCenter F| ≤
        (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / a ^ 2)) *
          (∫ rho in Ioi a, |F rho|) := by
    rw [actual_one_orbit_Vc_whole_mixed_Riesz_eq_exterior ell r hell,
      actual_one_orbit_Vc_whole_mixed_center_eq_exterior ell hell]
    exact actual_exteriorHartree_center_gap_L1_le
      F hFmeas hFext ha hr hsep'
  have hInv : 1 / a ^ 2 = 16 * ell ^ 2 := by
    dsimp [a]
    field_simp [hell.ne']
    ring
  refine ⟨hFull, ?_⟩
  calc
    |radialHartreePotential F r - radialHartreeCenter F| ≤
        (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / a ^ 2)) *
          (∫ rho in Ioi a, |F rho|) := hGap
    _ ≤ (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / a ^ 2)) *
          actualOneOrbitVcWholeMixedL1Envelope ell :=
      mul_le_mul_of_nonneg_left hL1 hκ
    _ = _ := by
      rw [hInv]
      ring

end HBL.TypeIIDynamicSelection
