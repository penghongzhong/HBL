import HBL.TypeIIDynamicSelection.ActualKummerPhysicalInterfaceRepair
import HBL.TypeIIDynamicSelection.ActualHartreeKummerTailTimeGain
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalOneLayerGain
import Mathlib.Tactic

/-!
# Physical Kummer interface repair has one genuine time gain

The now strictly replayed exact physical pullback contributes a^(-2). Under the same physical region
a >= L^3, L=ell^(-1/16), and ell(s)<=s^(-beta), this is stronger than
the already accepted Kummer tail gain 3 beta / 128. Hence a same-order
upper Kummer jet can be removed on the physical annulus [aR,2aR]
without losing the finite-profile gain.

No upper-jet estimate or remote nonlinear construction is assumed here.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The physical scale factor a^(-2) is bounded by the common physical
finite-profile time gain. -/
theorem actual_Hartree_physical_interface_repair_scale_time_gain
    (s ell a beta rhoStar : ℝ)
    (hs : 1 ≤ s) (hell : 0 < ell) (hellOne : ell ≤ 1)
    (ha3 : actualHartreeSlowInnerRadius ell ^ 3 ≤ a)
    (htrap : ell ≤ s ^ (-beta))
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4) :
    (a ^ 2)⁻¹ ≤
      s ^ (-actualHartreePhysicalKappa beta rhoStar) := by
  let L := actualHartreeSlowInnerRadius ell
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.rpow_pos_of_pos hell _
  have hLone : 1 ≤ L := by
    dsimp [L, actualHartreeSlowInnerRadius]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hell hellOne (by norm_num)
  have ha : 0 < a := (pow_pos hLpos 3).trans_le ha3
  have hsq0 :
      (L ^ 3) ^ 2 ≤ a ^ 2 :=
    pow_le_pow_left₀ (pow_nonneg hLpos.le 3) ha3 2
  have hL6 : L ^ 6 ≤ a ^ 2 := by
    calc
      L ^ 6 = (L ^ 3) ^ 2 := by ring
      _ ≤ a ^ 2 := hsq0
  have hinv :
      (a ^ 2)⁻¹ ≤ (L ^ 6)⁻¹ :=
    inv_anti₀ (pow_pos hLpos 6) hL6
  have hInvPow :
      (L ^ 6)⁻¹ = L ^ (-6 : ℝ) := by
    have hnat : L ^ (6 : ℝ) = L ^ (6 : ℕ) :=
      Real.rpow_natCast L 6
    calc
      (L ^ 6)⁻¹ = (L ^ (6 : ℝ))⁻¹ :=
        congrArg Inv.inv hnat.symm
      _ = L ^ (-6 : ℝ) :=
        (Real.rpow_neg hLpos.le (6 : ℝ)).symm
  have hExponent :
      L ^ (-6 : ℝ) ≤ L ^ (-(3 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  have hTail :=
    actual_Hartree_trapped_Kummer_tail_time_gain
      s ell beta hs hell htrap
  have hkTail :
      actualHartreePhysicalKappa beta rhoStar ≤
        actualHartreeKummerTailTimeGain beta := by
    simpa [actualHartreePhysicalGain] using
      (actual_Hartree_physical_kappa_le_gain
        beta rhoStar HBL.Profile.OneLayer.GainCause.frobenius)
  have hTime :
      s ^ (-actualHartreeKummerTailTimeGain beta) ≤
        s ^ (-actualHartreePhysicalKappa beta rhoStar) :=
    Real.rpow_le_rpow_of_exponent_le hs (neg_le_neg hkTail)
  calc
    (a ^ 2)⁻¹ ≤ (L ^ 6)⁻¹ := hinv
    _ = L ^ (-6 : ℝ) := hInvPow
    _ ≤ L ^ (-(3 / 8 : ℝ)) := hExponent
    _ = actualHartreeSlowInnerRadius ell ^ (-(3 / 8 : ℝ)) := rfl
    _ ≤ s ^ (-actualHartreeKummerTailTimeGain beta) := hTail
    _ ≤ s ^ (-actualHartreePhysicalKappa beta rhoStar) := hTime

/-- The COMPLETE frozen physical repair source is already in the next
physical layer. The Kummer-radius loss is explicit and fixed once R is fixed. -/
theorem actual_Hartree_Kummer_physical_interface_repair_next_layer :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
    ∀ (mu theta a R y s ell beta rhoStar : ℝ),
      0 < a → 0 < R → y ∈ Icc (a*R) (2*a*R) →
      1 ≤ s → 0 < ell → ell ≤ 1 →
      actualHartreeSlowInnerRadius ell ^ 3 ≤ a →
      ell ≤ s ^ (-beta) →
      1 / 2 < beta → 0 < rhoStar →
      rhoStar < (5 * beta - 2) / 4 →
    ∀ p q : ℂ,
      let D := ‖p‖ + R * ‖q‖
      let Krep :=
        (9*C2+12*C1+2)/R^2 + 3*C1+1+
          ‖frozenZeroCoeff mu theta‖
      ‖actualMatchedScaledKummerApply mu theta a
          (actualKummerPhysicalInterfaceRepair a R p q) y‖ ≤
        (Krep * D) *
          s ^ (-actualHartreePhysicalKappa beta rhoStar) := by
  obtain ⟨C1,C2,hC1,hC2,hRepair⟩ :=
    actual_Kummer_physical_interface_repair_residual_bound
  refine ⟨C1,C2,hC1,hC2,?_⟩
  intro mu theta a R y s ell beta rhoStar
    ha hR hy hs hell hellOne ha3 htrap hbeta hrhoStar hflat p q
  dsimp only
  let D := ‖p‖ + R * ‖q‖
  let Krep :=
    (9*C2+12*C1+2)/R^2 + 3*C1+1+
      ‖frozenZeroCoeff mu theta‖
  have hRaw := hRepair mu theta a R y ha hR hy p q
  have hScale :=
    actual_Hartree_physical_interface_repair_scale_time_gain
      s ell a beta rhoStar hs hell hellOne ha3 htrap
      hbeta hrhoStar hflat
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hKrep : 0 ≤ Krep := by
    dsimp [Krep]
    positivity
  have hKD : 0 ≤ Krep * D := mul_nonneg hKrep hD
  calc
    _ ≤ (a ^ 2)⁻¹ * Krep * D := by
      simpa only [D, Krep, mul_assoc] using hRaw
    _ = (a ^ 2)⁻¹ * (Krep * D) := by ring
    _ ≤ s ^ (-actualHartreePhysicalKappa beta rhoStar) *
        (Krep * D) :=
      mul_le_mul_of_nonneg_right hScale hKD
    _ = (Krep * D) *
        s ^ (-actualHartreePhysicalKappa beta rhoStar) := by ring

end HBL.TypeIIDynamicSelection
