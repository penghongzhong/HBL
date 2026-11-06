import HBL.TypeIIDynamicSelection.ActualKummerPhysicalInterfaceRepair
import HBL.TypeIIDynamicSelection.ExteriorSpatialGain
import Mathlib.Tactic

/-!
# Pure quartic Hartree feedback of the physical Kummer replacement tail

The physical interface repair is used only on the outer replacement annulus
(aR,2aR].  Its pure quartic density is therefore localized explicitly to
that annulus.  The already proved pointwise repair bound gives an L1 mass
at most (aR) D^4, where D=||p||+R||q||.

Combining this with the existing inverse-square exterior multipole theorem
gives a genuine geometric core gain
  |I_ext(r)-Center_ext| <= const * r^2/(aR) * D^4.

This controls only the PURE repair density and only its non-center part.
Mixed densities with the background and the exterior center itself remain
separate residuals; they are not hidden here.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualKummerPhysicalRepairOuterQuarticDensity
    (a R : ℝ) (p q : ℂ) (y : ℝ) : ℝ :=
  (Ioc (a * R) (2 * a * R)).indicator
    (fun x => ‖actualKummerPhysicalInterfaceRepair a R p q x‖ ^ 4) y

theorem actual_Kummer_physical_repair_outer_quartic_measurable
    (a R : ℝ) (ha : a ≠ 0) (hR : R ≠ 0) (p q : ℂ) :
    Measurable (actualKummerPhysicalRepairOuterQuarticDensity a R p q) := by
  have hCont : Continuous (actualKummerPhysicalInterfaceRepair a R p q) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (actual_Kummer_physical_interface_repair_derivatives
      a R y ha hR p q).1.continuousAt
  exact (hCont.norm.pow_const 4).measurable.indicator measurableSet_Ioc

/-- The localized pure repair density is globally integrable, with its
actual annulus length retained. -/
theorem actual_Kummer_physical_repair_outer_quartic_L1
    (a R : ℝ) (ha : 0 < a) (hR : 0 < R) (p q : ℂ) :
    let D := ‖p‖ + R * ‖q‖
    Integrable (actualKummerPhysicalRepairOuterQuarticDensity a R p q) ∧
    (∫ y in Ioi (a * R),
      |actualKummerPhysicalRepairOuterQuarticDensity a R p q y|) ≤
      (a * R) * D ^ 4 := by
  dsimp only
  let D : ℝ := ‖p‖ + R * ‖q‖
  let r0 : ℝ := a * R
  let r1 : ℝ := 2 * a * R
  let F : ℝ → ℝ := actualKummerPhysicalRepairOuterQuarticDensity a R p q
  have hr0 : 0 < r0 := mul_pos ha hR
  have hr01 : r0 ≤ r1 := by dsimp [r0, r1]; nlinarith [hr0]
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hMeas : Measurable F := by
    dsimp [F]
    exact actual_Kummer_physical_repair_outer_quartic_measurable
      a R ha.ne' hR.ne' p q
  have hSupport : Function.support F ⊆ Ioc r0 r1 := by
    intro y hy
    by_contra hmem
    have hz : F y = 0 := by
      dsimp [F, actualKummerPhysicalRepairOuterQuarticDensity, r0, r1]
      exact Set.indicator_of_notMem hmem _
    exact hy hz
  obtain ⟨C1,C2,_hC1,_hC2,hRepair⟩ :=
    actual_Kummer_interface_repair_positive_radius_bound
  have hBound (y : ℝ) : ‖F y‖ ≤ D ^ 4 := by
    by_cases hy : y ∈ Ioc r0 r1
    · have hyPhys : y / a ∈ Icc R (2 * R) := by
        constructor
        · apply (le_div_iff₀ ha).2
          simpa only [r0] using hy.1.le
        · apply (div_le_iff₀ ha).2
          simpa only [r1] using hy.2
      have hv := (hRepair 0 0 R (y / a) hR hyPhys p q).1
      have hpw : ‖actualKummerPhysicalInterfaceRepair a R p q y‖ ^ 4 ≤
          D ^ 4 := by
        dsimp [actualKummerPhysicalInterfaceRepair]
        exact pow_le_pow_left₀ (norm_nonneg _) hv 4
      dsimp [F, actualKummerPhysicalRepairOuterQuarticDensity]
      rw [Set.indicator_of_mem hy]
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
      exact hpw
    · dsimp [F, actualKummerPhysicalRepairOuterQuarticDensity]
      rw [Set.indicator_of_notMem hy, norm_zero]
      exact pow_nonneg hD 4
  have hCompact : HasCompactSupport F := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro y hy
    have h := hSupport hy
    exact ⟨h.1.le, h.2⟩
  have hLp : MemLp F 1 (volume : Measure ℝ) :=
    hCompact.memLp_of_bound hMeas.aestronglyMeasurable (D ^ 4)
      (Filter.Eventually.of_forall hBound)
  have hInt : Integrable F := (memLp_one_iff_integrable).mp hLp
  have hAbsSupport : Function.support (fun y => |F y|) ⊆ Ioc r0 r1 := by
    intro y hy
    apply hSupport
    intro hzero
    exact hy (by simp [hzero])
  have hAbsIoi : Function.support (fun y => |F y|) ⊆ Ioi r0 := by
    intro y hy
    exact (hAbsSupport hy).1
  have hAbsIcc : Function.support (fun y => |F y|) ⊆ Icc r0 r1 := by
    intro y hy
    have h := hAbsSupport hy
    exact ⟨h.1.le, h.2⟩
  have hEq :
      (∫ y in Ioi r0, |F y|) =
        ∫ y in Icc r0 r1, |F y| := by
    calc
      _ = ∫ y : ℝ, (Ioi r0).indicator (fun y => |F y|) y :=
        (integral_indicator measurableSet_Ioi).symm
      _ = ∫ y : ℝ, |F y| := by
        rw [indicator_eq_self.2 hAbsIoi]
      _ = ∫ y : ℝ, (Icc r0 r1).indicator (fun y => |F y|) y := by
        rw [indicator_eq_self.2 hAbsIcc]
      _ = _ := integral_indicator measurableSet_Icc
  have hfinite : (volume : Measure ℝ) (Icc r0 r1) < ⊤ := by
    simp only [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hAE : ∀ᵐ y : ℝ ∂volume,
      y ∈ Icc r0 r1 → ‖|F y|‖ ≤ D ^ 4 :=
    Filter.Eventually.of_forall (fun y _hy => by
      simpa only [Real.norm_eq_abs, abs_abs] using hBound y)
  have hNorm := norm_setIntegral_le_of_norm_le_const_ae'
    (μ := volume) (s := Icc r0 r1) (f := fun y => |F y|)
    (C := D ^ 4) hfinite hAE
  have hNorm' :
      ‖∫ y in Icc r0 r1, |F y|‖ ≤ D ^ 4 * r0 := by
    have hlen : r1 - r0 = r0 := by dsimp [r0, r1]; ring
    simpa only [Real.volume_real_Icc_of_le hr01, hlen] using hNorm
  have hL1 :
      (∫ y in Ioi r0, |F y|) ≤ r0 * D ^ 4 := by
    rw [hEq]
    calc
      _ ≤ |(∫ y in Icc r0 r1, |F y|)| := le_abs_self _
      _ = ‖∫ y in Icc r0 r1, |F y|‖ := (Real.norm_eq_abs _).symm
      _ ≤ D ^ 4 * r0 := hNorm'
      _ = r0 * D ^ 4 := by ring
  exact ⟨hInt, by simpa only [F, r0, D] using hL1⟩

/-- Pure outer repair density: the non-center inverse-square Hartree feedback
seen in the core gains one full inverse physical repair radius. -/
theorem actual_Kummer_physical_repair_outer_quartic_core_gap
    (a R r : ℝ) (ha : 0 < a) (hR : 0 < R)
    (hr : 0 < r) (hsep : 2 * r ≤ a * R) (p q : ℂ) :
    let D := ‖p‖ + R * ‖q‖
    let F := actualKummerPhysicalRepairOuterQuarticDensity a R p q
    |radialHartreeExteriorPotential F (a * R) r -
        radialHartreeExteriorCenter F (a * R)| ≤
      (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / (a * R))) * D ^ 4 := by
  dsimp only
  let D : ℝ := ‖p‖ + R * ‖q‖
  let F : ℝ → ℝ := actualKummerPhysicalRepairOuterQuarticDensity a R p q
  have hr0 : 0 < a * R := mul_pos ha hR
  have hM := actual_Kummer_physical_repair_outer_quartic_measurable
    a R ha.ne' hR.ne' p q
  have hL1 := actual_Kummer_physical_repair_outer_quartic_L1 a R ha hR p q
  have hGeo :=
    actual_exteriorHartree_center_gap_L1_le F hM hL1.1.integrableOn
      hr0 hr hsep
  have hcoef : 0 ≤
      4 * Real.pi * hartreeKappa * r ^ 2 * (1 / (a * R) ^ 2) := by
    unfold hartreeKappa
    positivity
  calc
    _ ≤ (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / (a * R) ^ 2)) *
        (∫ y in Ioi (a * R), |F y|) := hGeo
    _ ≤ (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / (a * R) ^ 2)) *
        ((a * R) * D ^ 4) :=
      mul_le_mul_of_nonneg_left hL1.2 hcoef
    _ = (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / (a * R))) *
        D ^ 4 := by
      field_simp [ha.ne', hR.ne']

end HBL.TypeIIDynamicSelection
