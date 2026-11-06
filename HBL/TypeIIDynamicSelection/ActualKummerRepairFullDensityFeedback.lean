import HBL.TypeIIDynamicSelection.ActualKummerRepairNonlocalFeedback
import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylor
import Mathlib.Tactic

/-!
# Full quartic Hartree density feedback of the physical Kummer replacement tail

On the physical replacement annulus (aR,2aR], let H be the actual Kummer
interface repair and U any measurable background with a uniform shell
amplitude A.  The exact quartic polynomial identity gives
  ||U+H||^4-||U||^4
as its real-linear term plus the complete quadratic/cubic/quartic remainder.

The already strict repair bound ||H||<=D, D=||p||+R||q||, yields the full
pointwise polynomial
  P(A,D)=4 A^3 D + 6 A^2 D^2 + 4 A D^3 + D^4.
The localized density difference therefore has L1 mass at most
  (aR) P(A,D).

Both the exterior Hartree center and the non-center core error are retained:
the center costs aR*P, while the geometric error gains r^2/(aR)*P.
No center cancellation or time order is assumed here.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualKummerRepairDensityPolynomial (A D : ℝ) : ℝ :=
  4 * A ^ 3 * D + 6 * A ^ 2 * D ^ 2 + 4 * A * D ^ 3 + D ^ 4

def actualKummerPhysicalRepairOuterDensityDifference
    (U : ℝ → ℂ) (a R : ℝ) (p q : ℂ) (y : ℝ) : ℝ :=
  (Ioc (a * R) (2 * a * R)).indicator
    (fun x =>
      ‖U x + actualKummerPhysicalInterfaceRepair a R p q x‖ ^ 4 -
        ‖U x‖ ^ 4) y

theorem actual_Kummer_repair_density_polynomial_nonneg
    (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    0 ≤ actualKummerRepairDensityPolynomial A D := by
  unfold actualKummerRepairDensityPolynomial
  positivity

theorem actual_Kummer_physical_repair_outer_density_difference_measurable
    (U : ℝ → ℂ) (hU : Measurable U)
    (a R : ℝ) (ha : a ≠ 0) (hR : R ≠ 0) (p q : ℂ) :
    Measurable
      (actualKummerPhysicalRepairOuterDensityDifference U a R p q) := by
  have hHcont : Continuous (actualKummerPhysicalInterfaceRepair a R p q) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (actual_Kummer_physical_interface_repair_derivatives
      a R y ha hR p q).1.continuousAt
  have hH : Measurable (actualKummerPhysicalInterfaceRepair a R p q) :=
    hHcont.measurable
  have hBase : Measurable (fun x =>
      ‖U x + actualKummerPhysicalInterfaceRepair a R p q x‖ ^ 4 -
        ‖U x‖ ^ 4) :=
    ((hU.add hH).norm.pow_const 4).sub (hU.norm.pow_const 4)
  exact hBase.indicator measurableSet_Ioc

theorem actual_Kummer_physical_repair_outer_density_difference_L1
    (U : ℝ → ℂ) (hUmeas : Measurable U)
    (a R A : ℝ) (ha : 0 < a) (hR : 0 < R) (hA : 0 ≤ A)
    (p q : ℂ)
    (hU : ∀ y ∈ Ioc (a * R) (2 * a * R), ‖U y‖ ≤ A) :
    let D := ‖p‖ + R * ‖q‖
    let P := actualKummerRepairDensityPolynomial A D
    Integrable (actualKummerPhysicalRepairOuterDensityDifference U a R p q) ∧
    (∫ y in Ioi (a * R),
      |actualKummerPhysicalRepairOuterDensityDifference U a R p q y|) ≤
      (a * R) * P := by
  dsimp only
  let D : ℝ := ‖p‖ + R * ‖q‖
  let P : ℝ := actualKummerRepairDensityPolynomial A D
  let r0 : ℝ := a * R
  let r1 : ℝ := 2 * a * R
  let H : ℝ → ℂ := actualKummerPhysicalInterfaceRepair a R p q
  let F : ℝ → ℝ :=
    actualKummerPhysicalRepairOuterDensityDifference U a R p q
  have hr0 : 0 < r0 := mul_pos ha hR
  have hr01 : r0 ≤ r1 := by dsimp [r0, r1]; nlinarith [hr0]
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hP : 0 ≤ P :=
    actual_Kummer_repair_density_polynomial_nonneg A D hA hD
  have hMeas : Measurable F := by
    dsimp [F]
    exact actual_Kummer_physical_repair_outer_density_difference_measurable
      U hUmeas a R ha.ne' hR.ne' p q
  have hSupport : Function.support F ⊆ Ioc r0 r1 := by
    intro y hy
    by_contra hmem
    have hz : F y = 0 := by
      dsimp [F, actualKummerPhysicalRepairOuterDensityDifference, r0, r1]
      exact Set.indicator_of_notMem hmem _
    exact hy hz
  obtain ⟨C1,C2,_hC1,_hC2,hRepair⟩ :=
    actual_Kummer_interface_repair_positive_radius_bound
  have hBound (y : ℝ) : ‖F y‖ ≤ P := by
    by_cases hy : y ∈ Ioc r0 r1
    · have hyPhys : y / a ∈ Icc R (2 * R) := by
        constructor
        · apply (le_div_iff₀ ha).2
          simpa only [r0, mul_comm] using hy.1.le
        · apply (div_le_iff₀ ha).2
          simpa only [r1, mul_assoc, mul_comm, mul_left_comm] using hy.2
      have hHv := (hRepair 0 0 R (y / a) hR hyPhys p q).1
      have hHphysical : ‖H y‖ ≤ D := by
        dsimp [H, actualKummerPhysicalInterfaceRepair]
        exact hHv
      have hPoly :=
        actual_Hartree_complex_Taylor_polynomial_bounds
          (U y) (H y) hA hD (hU y hy) hHphysical
      have hId :
          ‖U y + H y‖ ^ 4 - ‖U y‖ ^ 4 =
            actualHartreeComplexDensityLinear (U y) (H y) +
              actualHartreeComplexDensityRemainder (U y) (H y) := by
        have h :=
          (actual_Hartree_complex_Taylor_polynomial_identity (U y) (H y)).1
        linarith
      have hAbs :
          |‖U y + H y‖ ^ 4 - ‖U y‖ ^ 4| ≤ P := by
        rw [hId]
        calc
          _ ≤ |actualHartreeComplexDensityLinear (U y) (H y)| +
              |actualHartreeComplexDensityRemainder (U y) (H y)| :=
            abs_add_le _ _
          _ ≤ 4 * A ^ 3 * D +
              (6 * A ^ 2 * D ^ 2 + 4 * A * D ^ 3 + D ^ 4) :=
            add_le_add hPoly.1 hPoly.2.1
          _ = P := by
            dsimp [P, actualKummerRepairDensityPolynomial]
            ring
      dsimp [F, actualKummerPhysicalRepairOuterDensityDifference]
      rw [Set.indicator_of_mem hy]
      change |‖U y + H y‖ ^ 4 - ‖U y‖ ^ 4| ≤ P
      exact hAbs
    · dsimp [F, actualKummerPhysicalRepairOuterDensityDifference]
      rw [Set.indicator_of_notMem hy]
      simpa only [abs_zero] using hP
  have hCompact : HasCompactSupport F := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro y hy
    have h := hSupport hy
    exact ⟨h.1.le, h.2⟩
  have hLp : MemLp F 1 (volume : Measure ℝ) :=
    hCompact.memLp_of_bound hMeas.aestronglyMeasurable P
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
      y ∈ Icc r0 r1 → ‖|F y|‖ ≤ P :=
    Filter.Eventually.of_forall (fun y _hy => by
      simpa only [Real.norm_eq_abs, abs_abs] using hBound y)
  have hNorm := norm_setIntegral_le_of_norm_le_const_ae'
    (μ := volume) (s := Icc r0 r1) (f := fun y => |F y|)
    (C := P) hfinite hAE
  have hNorm' :
      ‖∫ y in Icc r0 r1, |F y|‖ ≤ P * r0 := by
    have hlen : r1 - r0 = r0 := by dsimp [r0, r1]; ring
    simpa only [Real.volume_real_Icc_of_le hr01, hlen] using hNorm
  have hL1 :
      (∫ y in Ioi r0, |F y|) ≤ r0 * P := by
    rw [hEq]
    calc
      _ ≤ |(∫ y in Icc r0 r1, |F y|)| := le_abs_self _
      _ = ‖∫ y in Icc r0 r1, |F y|‖ := (Real.norm_eq_abs _).symm
      _ ≤ P * r0 := hNorm'
      _ = r0 * P := by ring
  exact ⟨hInt, by simpa only [F, r0, P, D] using hL1⟩

theorem actual_Kummer_physical_repair_outer_density_center_bound
    (U : ℝ → ℂ) (hUmeas : Measurable U)
    (a R A : ℝ) (ha : 0 < a) (hR : 0 < R) (hA : 0 ≤ A)
    (p q : ℂ)
    (hU : ∀ y ∈ Ioc (a * R) (2 * a * R), ‖U y‖ ≤ A) :
    let D := ‖p‖ + R * ‖q‖
    let P := actualKummerRepairDensityPolynomial A D
    let F := actualKummerPhysicalRepairOuterDensityDifference U a R p q
    |radialHartreeExteriorCenter F (a * R)| ≤
      (4 * Real.pi * hartreeKappa) * ((a * R) * P) := by
  dsimp only
  let D : ℝ := ‖p‖ + R * ‖q‖
  let P : ℝ := actualKummerRepairDensityPolynomial A D
  let F : ℝ → ℝ :=
    actualKummerPhysicalRepairOuterDensityDifference U a R p q
  have hL1 :=
    actual_Kummer_physical_repair_outer_density_difference_L1
      U hUmeas a R A ha hR hA p q hU
  have hk : 0 ≤ 4 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  unfold radialHartreeExteriorCenter
  rw [abs_mul, abs_of_nonneg hk]
  calc
    (4 * Real.pi * hartreeKappa) *
        |∫ y in Ioi (a * R), F y| ≤
      (4 * Real.pi * hartreeKappa) *
        (∫ y in Ioi (a * R), |F y|) :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hk
    _ ≤ (4 * Real.pi * hartreeKappa) * ((a * R) * P) :=
      mul_le_mul_of_nonneg_left hL1.2 hk

theorem actual_Kummer_physical_repair_outer_density_core_gap
    (U : ℝ → ℂ) (hUmeas : Measurable U)
    (a R A r : ℝ) (ha : 0 < a) (hR : 0 < R) (hA : 0 ≤ A)
    (hr : 0 < r) (hsep : 2 * r ≤ a * R)
    (p q : ℂ)
    (hU : ∀ y ∈ Ioc (a * R) (2 * a * R), ‖U y‖ ≤ A) :
    let D := ‖p‖ + R * ‖q‖
    let P := actualKummerRepairDensityPolynomial A D
    let F := actualKummerPhysicalRepairOuterDensityDifference U a R p q
    |radialHartreeExteriorPotential F (a * R) r -
        radialHartreeExteriorCenter F (a * R)| ≤
      (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / (a * R))) * P := by
  dsimp only
  let D : ℝ := ‖p‖ + R * ‖q‖
  let P : ℝ := actualKummerRepairDensityPolynomial A D
  let F : ℝ → ℝ :=
    actualKummerPhysicalRepairOuterDensityDifference U a R p q
  have hr0 : 0 < a * R := mul_pos ha hR
  have hM :=
    actual_Kummer_physical_repair_outer_density_difference_measurable
      U hUmeas a R ha.ne' hR.ne' p q
  have hL1 :=
    actual_Kummer_physical_repair_outer_density_difference_L1
      U hUmeas a R A ha hR hA p q hU
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
        ((a * R) * P) :=
      mul_le_mul_of_nonneg_left hL1.2 hcoef
    _ = (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / (a * R))) *
        P := by
      field_simp [ha.ne', hR.ne']

end HBL.TypeIIDynamicSelection
