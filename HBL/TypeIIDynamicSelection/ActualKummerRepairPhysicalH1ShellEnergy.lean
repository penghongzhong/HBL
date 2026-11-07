import HBL.TypeIIDynamicSelection.ActualKummerPhysicalInterfaceRepair
import Mathlib.Tactic

/-!
# Actual physical Kummer repair: radial Hdot1 energy on its replacement shell

The physical 3D radial gradient energy carries the exact r² measure.
On [aR,2aR], the concrete scaled repair has derivative of size D/(aR),
where D=||p||+R||q|| is the ORIGINAL matched boundary jet.

The resulting genuine radial-gradient energy is bounded by
  integral_[aR,2aR] r² |H'_rep(r)|² dr <= C (aR) D².
No abstract regional energy assumption or independent repair field appears.
The additional time gain follows after inserting the physical clock and
the uniquely selected source-to-jet bound, not by assigning an energy order.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- The actual Kummer interface repair has quantitative 3D radial
gradient energy on the physical dyadic replacement annulus. -/
theorem actual_Kummer_physical_interface_repair_radial_shell_H1_energy :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ (a R : ℝ), 0 < a → 0 < R →
      ∀ (p q : ℂ),
      let D := ‖p‖ + R * ‖q‖
      (∫ y in Icc (a * R) (2 * a * R),
        y ^ 2 *
          ‖deriv (actualKummerPhysicalInterfaceRepair a R p q) y‖ ^ 2) ≤
        (4 * (3 * C1 + 1) ^ 2) * (a * R) * D ^ 2 := by
  obtain ⟨C1, C2, hC1, hC2, hRepair⟩ :=
    actual_Kummer_interface_repair_positive_radius_bound
  refine ⟨C1,C2,hC1,hC2,?_⟩
  intro a R ha hR p q
  dsimp only
  let r0 : ℝ := a * R
  let r1 : ℝ := 2 * a * R
  let D : ℝ := ‖p‖ + R * ‖q‖
  let C0 : ℝ := 4 * (3 * C1 + 1) ^ 2 * D ^ 2
  let rep : ℝ → ℂ := actualKummerPhysicalInterfaceRepair a R p q
  have hr0 : 0 < r0 := mul_pos ha hR
  have hr01 : r0 ≤ r1 := by dsimp [r0,r1]; linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hDeriv (y : ℝ) :
      deriv rep y = actualKummerPhysicalInterfaceRepairSlope a R p q y :=
    (actual_Kummer_physical_interface_repair_derivatives
      a R y ha.ne' hR.ne' p q).1.deriv
  have hSlopeCont : Continuous
      (actualKummerPhysicalInterfaceRepairSlope a R p q) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (actual_Kummer_physical_interface_repair_derivatives
      a R y ha.ne' hR.ne' p q).2.continuousAt
  have hDerivCont : Continuous (fun y => deriv rep y) := by
    convert hSlopeCont using 1
    funext y
    exact hDeriv y
  let f : ℝ → ℝ := fun y => y ^ 2 * ‖deriv rep y‖ ^ 2
  have hFcont : Continuous f :=
    (continuous_id.pow 2).mul (hDerivCont.norm.pow 2)
  have hFmeas : AEStronglyMeasurable f (volume : Measure ℝ) :=
    hFcont.measurable.aestronglyMeasurable
  have hBound (y : ℝ) (hy : y ∈ Icc r0 r1) :
      f y ≤ C0 := by
    have hy0 : 0 ≤ y := hr0.le.trans hy.1
    have hyPhys : y / a ∈ Icc R (2 * R) := by
      constructor
      · exact (le_div_iff₀ ha).2
          (by simpa only [r0,mul_comm] using hy.1)
      · exact (div_le_iff₀ ha).2
          (by simpa only [r1,mul_assoc,mul_comm,mul_left_comm] using hy.2)
    have hRaw := (hRepair 0 0 R (y/a) hR hyPhys p q).2.1
    have hPos : 0 < 1 / a := one_div_pos.mpr ha
    have hDerivBound :
        ‖deriv rep y‖ ≤ (3 * C1 + 1) * D / (a * R) := by
      rw [hDeriv]
      unfold actualKummerPhysicalInterfaceRepairSlope
      simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos hPos]
      calc
        (1 / a) * ‖actualKummerInterfaceRepairSlope R p q (y / a)‖ ≤
          (1 / a) * ((3 * C1 + 1) * D / R) :=
          mul_le_mul_of_nonneg_left
            (by simpa only [D] using hRaw) hPos.le
        _ = (3 * C1 + 1) * D / (a * R) := by
          field_simp [ha.ne',hR.ne']
    have hYDeriv :
        y * ‖deriv rep y‖ ≤ 2 * (3 * C1 + 1) * D := by
      calc
        _ ≤ (2 * a * R) * ((3 * C1 + 1) * D / (a * R)) :=
          mul_le_mul
            (by simpa only [r1,mul_assoc,mul_comm,mul_left_comm] using hy.2)
            hDerivBound (norm_nonneg _) (by positivity)
        _ = 2 * (3 * C1 + 1) * D := by
          field_simp [ha.ne',hR.ne']
    have hY0 : 0 ≤ y * ‖deriv rep y‖ :=
      mul_nonneg hy0 (norm_nonneg _)
    calc
      f y = (y * ‖deriv rep y‖) ^ 2 := by dsimp [f]; ring
      _ ≤ (2 * (3 * C1 + 1) * D) ^ 2 :=
        pow_le_pow_left₀ hY0 hYDeriv 2
      _ = C0 := by dsimp [C0]; ring
  have hFinite : (volume : Measure ℝ) (Icc r0 r1) < ⊤ := by
    simp only [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hAE : ∀ᵐ y : ℝ ∂volume, y ∈ Icc r0 r1 →
      ‖f y‖ ≤ C0 := by
    filter_upwards with y
    intro hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [f]; positivity)]
    exact hBound y hy
  have hNorm := norm_setIntegral_le_of_norm_le_const_ae'
    (μ := volume) (s := Icc r0 r1) (f := f)
    (C := C0) hFinite hAE
  have hLen : r1 - r0 = r0 := by dsimp [r0,r1]; ring
  have hResult : ‖∫ y in Icc r0 r1, f y‖ ≤ C0 * r0 := by
    simpa only [Real.volume_real_Icc_of_le hr01, hLen] using hNorm
  calc
    (∫ y in Icc (a * R) (2 * a * R),
      y ^ 2 *
          ‖deriv (actualKummerPhysicalInterfaceRepair a R p q) y‖ ^ 2) =
        ∫ y in Icc r0 r1, f y := by rfl
    _ ≤ ‖∫ y in Icc r0 r1, f y‖ :=
      (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm
    _ ≤ C0 * r0 := hResult
    _ = (4 * (3 * C1 + 1) ^ 2) * (a * R) * D ^ 2 := by
      dsimp [C0,r0]
      ring

end HBL.TypeIIDynamicSelection
