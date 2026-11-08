import HBL.TypeIIDynamicSelection.ActualHartreePhysicalKummerC1Splice
import HBL.TypeIIDynamicSelection.ActualKummerRepairPhysicalH1TimeGain
import Mathlib.Tactic

/-!
# One actual Kummer source: exact equation, physical C1 gluing and H1 gain

This single certificate reuses the SAME origin-normalized forced Green
solution and its genuinely selected right value/slope jet.
The physical pullback solves its exact forced scaled Kummer equation,
the Kummer / repair / zero continuation is differentiable with the
correct two physical interface derivatives, and the compact replacement
has a strictly positive three-dimensional radial Hdot1 shell gain.

The upper jet's source decay remains an explicit premise to be supplied
by the actual coupled Hartree compatibility producer. Neither a free
homogeneous amplitude nor a prescribed Type-II rate is introduced.
This is one physical Kummer component, not the full three-region profile.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_physical_matched_Kummer_C1_PDE_and_H1_certificate
    {mu theta scale r0 B : ℝ} (K : OriginKummerPair mu theta scale)
    (a s beta rho CX CD : ℝ)
    (ha : 0 < a) (hr0 : 0 < r0) (horder : r0 ≤ B)
    (hB : B < scale) (hs : 1 ≤ s)
    (hbeta : 1 / 2 < beta)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (hCX : 0 ≤ CX) (hCD : 0 ≤ CD)
    (hX : a * B ≤ CX * s ^ (1 / 2 : ℝ))
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r)
    (U DU : ℂ)
    (hJet :
      ‖actualOriginMatchedKummerValue K r0 B F U DU B‖ +
        B * ‖actualOriginMatchedKummerSlope K r0 B F U DU B‖ ≤
      CD * s ^ (-rho)) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      let w := actualOriginMatchedKummerValue K r0 B F U DU
      let v := actualOriginMatchedKummerPullback K a r0 B F U DU
      let UB := w B
      let DUB := actualOriginMatchedKummerSlope K r0 B F U DU B
      let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
      let glued := actualPhysicalMatchedKummerC1Splice a B v rep
      (∀ y ∈ Ioo 0 (a * scale),
        actualMatchedScaledKummerApply mu theta a v y =
          ((a ^ 2)⁻¹ : ℝ) • F (y / a)) ∧
      HasDerivAt glued ((1 / a : ℝ) • DUB) (a * B) ∧
      HasDerivAt glued 0 (2 * a * B) ∧
      (∫ y in Icc (a * B) (2 * a * B),
        y ^ 2 * ‖deriv rep y‖ ^ 2) ≤
        (4 * (3 * C1 + 1) ^ 2 * CX * CD ^ 2) *
          s ^ (-actualKummerRepairCenterTimeGain beta) := by
  obtain ⟨C1,C2,hC1,hC2,hEnergy⟩ :=
    actual_Kummer_physical_repair_shell_H1_positive_time_gain
  refine ⟨C1,C2,hC1,hC2,?_⟩
  dsimp only
  let w := actualOriginMatchedKummerValue K r0 B F U DU
  let v := actualOriginMatchedKummerPullback K a r0 B F U DU
  let UB := w B
  let DUB := actualOriginMatchedKummerSlope K r0 B F U DU B
  let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
  let glued := actualPhysicalMatchedKummerC1Splice a B v rep
  have hEquation (y : ℝ) (hy : y ∈ Ioo 0 (a * scale)) :
      actualMatchedScaledKummerApply mu theta a v y =
        ((a ^ 2)⁻¹ : ℝ) • F (y / a) := by
    exact (actual_Hartree_matched_Kummer_pullback_classical
      K a ha hr0 horder hB F hF U DU y hy).2.2
  have hJoins :=
    actual_Hartree_matched_Kummer_repair_is_C1_at_both_physical_joins
      K a ha hr0 horder hB F hF U DU
  have hBpos : 0 < B := hr0.trans_le horder
  have hEnergyBound :=
    hEnergy a B s beta rho CX CD ha hBpos hs hbeta
      hrho hCX hCD hX UB DUB (by
        simpa only [w, UB, DUB] using hJet)
  dsimp only at hJoins hEnergyBound
  refine ⟨hEquation, ?_, ?_, ?_⟩
  · simpa only [glued, v, rep, w, UB, DUB] using hJoins.1
  · simpa only [glued, v, rep, w, UB, DUB] using hJoins.2
  · simpa only [rep, w, UB, DUB] using hEnergyBound.2

end HBL.TypeIIDynamicSelection
