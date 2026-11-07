import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedKummerPullback
import HBL.TypeIIDynamicSelection.ActualKummerPhysicalInterfaceRepair
import Mathlib.Tactic

/-!
# True two-interface C1 jet matching of the origin-normalized Kummer solve

Take the SAME complete forced origin Green solution and its actual right
value/slope at the fixed small Kummer radius B. Replace its outer continuation
by the physical Kummer repair with precisely this jet (not its negative).

At the physical junction y=a B the value and ordinary derivative agree;
at y=2 a B the repair and derivative both vanish. This uses the genuine
pullback derivative, original source and actual Cramer Green continuation.

It is the exact C1 trace condition needed for global physical gluing.
Regional Hdot1 bounds and nonlinear residual iteration remain separate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Two physical C1 interface jets for the SAME original forced Kummer
solution and the concrete compact replacement tail. -/
theorem actual_Hartree_matched_Kummer_physical_repair_two_C1_jets
    {mu theta scale r0 B : ℝ} (K : OriginKummerPair mu theta scale)
    (a : ℝ) (ha : 0 < a)
    (hr0 : 0 < r0) (horder : r0 ≤ B) (hB : B < scale)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r)
    (U DU : ℂ) :
    let w := actualOriginMatchedKummerValue K r0 B F U DU
    let v := actualOriginMatchedKummerPullback K a r0 B F U DU
    let UB := w B
    let DUB := actualOriginMatchedKummerSlope K r0 B F U DU B
    let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
    v (a * B) = rep (a * B) ∧
    deriv v (a * B) = deriv rep (a * B) ∧
    rep (2 * a * B) = 0 ∧
    deriv rep (2 * a * B) = 0 := by
  dsimp only
  let w := actualOriginMatchedKummerValue K r0 B F U DU
  let v := actualOriginMatchedKummerPullback K a r0 B F U DU
  let UB := w B
  let DUB := actualOriginMatchedKummerSlope K r0 B F U DU B
  let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
  have hBpos : 0 < B := hr0.trans_le horder
  have hscale : 0 < scale := hBpos.trans hB
  have hDomain : a * B ∈ Ioo (0 : ℝ) (a * scale) := by
    constructor
    · exact mul_pos ha hBpos
    · exact mul_lt_mul_of_pos_left hB ha
  have hPhysical :=
    actual_Hartree_matched_Kummer_pullback_classical
      K a ha hr0 horder hB F hF U DU (a * B) hDomain
  have hK :
      deriv w B = DUB := by
    exact (actual_origin_matched_Kummer_classical_on_positive_interval
      K hr0 horder hB F hF U DU B
      ⟨hBpos, hB⟩).1.deriv
  have hAt : (a * B) / a = B := by field_simp [ha.ne']
  have hv : v (a * B) = UB := by
    dsimp [v, UB, actualOriginMatchedKummerPullback]
    rw [hAt]
  have hdv : deriv v (a * B) = (1 / a : ℝ) • DUB := by
    have hh := hPhysical.1.deriv
    change deriv v (a * B) =
      (a : ℂ)⁻¹ * deriv w ((a * B) / a) at hh
    rw [hAt, hK] at hh
    simpa only [Complex.real_smul, Complex.ofReal_inv, one_div] using hh
  have hRepair :=
    actual_Kummer_physical_interface_repair_endpoint_jets
      a B ha hBpos UB DUB
  have hderivLeft :=
    (actual_Kummer_physical_interface_repair_derivatives
      a B (a * B) ha.ne' hBpos.ne' UB DUB).1.deriv
  have hderivRight :=
    (actual_Kummer_physical_interface_repair_derivatives
      a B (2 * a * B) ha.ne' hBpos.ne' UB DUB).1.deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hv.trans hRepair.1.symm
  · rw [hdv, hderivLeft]
    exact hRepair.2.1.symm
  · exact hRepair.2.2.1
  · rw [hderivRight]
    exact hRepair.2.2.2

end HBL.TypeIIDynamicSelection
