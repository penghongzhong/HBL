import HBL.TypeIIDynamicSelection.ActualOneOrbitMovingMonopoleCenter
import HBL.TypeIIDynamicSelection.ExteriorSpatialGain
import Mathlib.Tactic

/-!
# Actual V_c nonlocal Hartree linear mixed source: inner Riesz matching

This is the physical moment-generated monopole V_c, not the W-only
surrogate. The true Hartree inverse-square radial potential of
4 V_c^3 Re Z_ell is shown to equal its exterior potential, with the
exact same source as the full original convolution.

The previously established absolute L1 mass O(ell^(5/2)), the genuine
exterior multipole estimate and the exact physical support give a
quantitative O(r^2 ell^(9/2)) core centre defect. The conclusion
includes absolute convergence of the original full Hartree Riesz row.
No blowup rate or abstract source inverse appears as an input.

This is a component of original manuscript 2.12, not its complete
two-threshold/Kummer/remote/PDE matching.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

private theorem actual_one_orbit_Vc_mixed_zero_below
    (ell : ℝ) (hell : 0 < ell) {r : ℝ}
    (hr : r ≤ 1 / (4 * ell)) :
    actualOneOrbitMovingMixedLinear ell r = 0 := by
  have hz := actual_one_orbit_rescaled_terminal_zero_core ell r hell hr
  simp [actualOneOrbitMovingMixedLinear, hz]

/-- The actual quartic density is literally its physical exterior
indicator; the physical radiation is not replaced by a model forcing. -/
theorem actual_one_orbit_Vc_mixed_exterior_indicator
    (ell : ℝ) (hell : 0 < ell) :
    (Ioi (1 / (4 * ell))).indicator
        (actualOneOrbitMovingMixedLinear ell) =
      actualOneOrbitMovingMixedLinear ell := by
  funext rho
  by_cases h : rho ∈ Ioi (1 / (4 * ell))
  · simp only [Set.indicator_of_mem h]
  · have hbelow : rho ≤ 1 / (4 * ell) :=
      le_of_not_gt (by simpa only [mem_Ioi] using h)
    have hz := actual_one_orbit_Vc_mixed_zero_below ell hell
      (r := rho) hbelow
    simp only [Set.indicator_of_notMem h, hz]

/-- Exact *total* Hartree centre is the exterior centre of the same
moment-selected V_c mixed density. -/
theorem actual_one_orbit_Vc_mixed_center_eq_exterior
    (ell : ℝ) (hell : 0 < ell) :
    radialHartreeCenter (actualOneOrbitMovingMixedLinear ell) =
      radialHartreeExteriorCenter
        (actualOneOrbitMovingMixedLinear ell) (1 / (4 * ell)) := by
  let F : ℝ → ℝ := actualOneOrbitMovingMixedLinear ell
  let a : ℝ := 1 / (4 * ell)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsubset : Ioi a ⊆ Ioi (0 : ℝ) :=
    fun x hx => lt_of_le_of_lt ha hx
  have hmask : (Ioi a).indicator F = F := by
    simpa only [F, a] using
      actual_one_orbit_Vc_mixed_exterior_indicator ell hell
  have hintEq :
      (∫ rho in Ioi (0 : ℝ), F rho) =
        ∫ rho in Ioi a, F rho := by
    calc
      _ = ∫ rho in Ioi (0 : ℝ), (Ioi a).indicator F rho := by rw [hmask]
      _ = ∫ rho in Ioi (0 : ℝ) ∩ Ioi a, F rho :=
        setIntegral_indicator measurableSet_Ioi
      _ = ∫ rho in Ioi a, F rho := by
        rw [inter_eq_right.mpr hsubset]
  unfold radialHartreeCenter radialHartreeExteriorCenter
  rw [hintEq]

/-- For the genuine time-terminal V_c field, the original half-line
Riesz integral is precisely the physical exterior integral, at EVERY
observation point; no support hypothesis is added. -/
theorem actual_one_orbit_Vc_mixed_Riesz_eq_exterior
    (ell r : ℝ) (hell : 0 < ell) :
    radialHartreePotential (actualOneOrbitMovingMixedLinear ell) r =
      radialHartreeExteriorPotential
        (actualOneOrbitMovingMixedLinear ell) (1 / (4 * ell)) r := by
  have hmask := actual_one_orbit_Vc_mixed_exterior_indicator ell hell
  rw [radialHartreeExteriorPotential_eq_indicator
        (actualOneOrbitMovingMixedLinear ell)
        (by positivity : 0 ≤ 1 / (4 * ell)) r]
  rw [hmask]

/-- On 0 < 2r <= 1/(4ell), the original actual inverse-square Hartree
Riesz potential of the full V_c mixed density differs from the exact
physical monopole threshold charge by O(r² ell^(9/2)).

This simultaneously establishes the required absolute Riesz-row
integrability, rather than relying on integral totalization. -/
theorem actual_one_orbit_Vc_mixed_Riesz_inner_length_gain
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (hsep : 2 * r ≤ 1 / (4 * ell)) :
    IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualOneOrbitMovingMixedLinear ell rho) (Ioi (0 : ℝ)) ∧
    |radialHartreePotential (actualOneOrbitMovingMixedLinear ell) r -
        radialHartreeCenter (actualOneOrbitMovingMixedLinear ell)| ≤
      (960 * Real.pi * hartreeKappa *
        actualOneOrbitMovingEnvelope ^ 3) *
          r ^ 2 * ell ^ 4 * Real.sqrt ell := by
  let F : ℝ → ℝ := actualOneOrbitMovingMixedLinear ell
  let a : ℝ := 1 / (4 * ell)
  have ha : 0 < a := by dsimp [a]; positivity
  have hmeas : Measurable F :=
    actual_one_orbit_Vc_mixed_source_measurable ell
  have hSource :=
    actual_one_orbit_Vc_mixed_Hartree_center_L1_five_halves_gain ell hell
  have hFext : IntegrableOn F (Ioi a) :=
    hSource.1.integrableOn.mono_set (fun x hx => ha.trans hx)
  have hsep' : 2 * r ≤ a := hsep
  obtain ⟨_hWeighted, hrow, _hError⟩ :=
    radialHartreeExteriorPotential_quadratic_center
      F hmeas hFext ha hr hsep'
  let G : ℝ → ℝ :=
    fun rho => rho * hartreeRadialLog r rho * F rho
  have hnear : IntegrableOn G (Ioc (0 : ℝ) a) := by
    apply integrableOn_zero.congr_fun ?_ measurableSet_Ioc
    intro rho hρ
    have hz := actual_one_orbit_Vc_mixed_zero_below ell hell
      (r := rho) hρ.2
    simp [G, F, hz]
  have hfull : IntegrableOn G (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact hnear.union hrow
  have hsubset : Ioi a ⊆ Ioi (0 : ℝ) :=
    fun x hx => ha.trans hx
  have hAbsMask :
      (Ioi a).indicator (fun rho => |F rho|) =
        (fun rho => |F rho|) := by
    funext rho
    by_cases h : rho ∈ Ioi a
    · simp only [Set.indicator_of_mem h]
    · have hbelow : rho ≤ a :=
        le_of_not_gt (by simpa only [mem_Ioi] using h)
      have hz := actual_one_orbit_Vc_mixed_zero_below ell hell
        (r := rho) hbelow
      rw [Set.indicator_of_notMem h]
      have hfzero : F rho = 0 := hz
      rw [hfzero, abs_zero]
  have hAbsEq :
      (∫ rho in Ioi a, |F rho|) =
        ∫ rho in Ioi (0 : ℝ), |F rho| := by
    calc
      _ = ∫ rho in Ioi (0 : ℝ) ∩ Ioi a, |F rho| := by
        rw [inter_eq_right.mpr hsubset]
      _ = ∫ rho in Ioi (0 : ℝ),
            (Ioi a).indicator (fun rho => |F rho|) rho :=
        (setIntegral_indicator measurableSet_Ioi).symm
      _ = ∫ rho in Ioi (0 : ℝ), |F rho| := by
        rw [hAbsMask]
  have hL1 : (∫ rho in Ioi a, |F rho|) ≤
      15 * actualOneOrbitMovingEnvelope ^ 3 *
        ell ^ 2 * Real.sqrt ell := by
    rw [hAbsEq]
    exact hSource.2.1
  have hκ : 0 ≤
      4 * Real.pi * hartreeKappa * r ^ 2 * (1 / a ^ 2) := by
    unfold hartreeKappa
    positivity
  have hGeom : |radialHartreePotential F r - radialHartreeCenter F| ≤
      (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / a ^ 2)) *
        (∫ rho in Ioi a, |F rho|) := by
    rw [actual_one_orbit_Vc_mixed_Riesz_eq_exterior ell r hell,
      actual_one_orbit_Vc_mixed_center_eq_exterior ell hell]
    exact actual_exteriorHartree_center_gap_L1_le
      F hmeas hFext ha hr hsep'
  have hRinv : 1 / a ^ 2 = 16 * ell ^ 2 := by
    dsimp [a]
    field_simp [hell.ne']
    ring
  refine ⟨hfull, ?_⟩
  calc
    |radialHartreePotential F r - radialHartreeCenter F| ≤
        (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / a ^ 2)) *
          (∫ rho in Ioi a, |F rho|) := hGeom
    _ ≤ (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / a ^ 2)) *
          (15 * actualOneOrbitMovingEnvelope ^ 3 *
            ell ^ 2 * Real.sqrt ell) :=
        mul_le_mul_of_nonneg_left hL1 hκ
    _ = _ := by
      rw [hRinv]
      ring

end HBL.TypeIIDynamicSelection
