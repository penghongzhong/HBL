import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCoupledDeterminantBound
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedResponseMomentGrowth
import HBL.TypeIIDynamicSelection.CoupledSmallParameterRegion

/-!
A concrete nondegenerate parameter region for the complete moment-locked
compatibility matrix. The physical profile error constant and the actual
Fredholm response growth bounds are derived inside the proof. The final
hypotheses contain no free trace, small Green moment, small total error,
nonzero reference integral, or nonzero determinant assumption.

The Kummer coefficient and solution bounds concern the actual origin IVP.
The conclusion is a frozen-configuration matrix estimate; it does not assert
that a nonlinear trajectory has already been trapped in this region.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.Kummer

/-- Actual complete-column nondegeneracy on an explicit small-parameter
region. Both physical sources, their forced charges, and their reconstructed
traces remain those of the original moment-locked Fredholm construction. -/
theorem actual_Hartree_moment_locked_coupled_nondegenerate_region
    {mu theta R B : ℝ} (K : OriginKummerPair mu theta R)
    (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B) (hBR : B < R)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon : ℝ, 3 ≤ L0 ∧ 0 < epsilon ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → |c| ≤ 1 → a * |c| ≤ epsilon →
        a ^ 2 * B ^ 4 / 256 ≤
          actualMomentLockedCoupledDeterminant K L c hLp a (L / a) B ∧
        0 < actualMomentLockedCoupledDeterminant K L c hLp a (L / a) B := by
  obtain ⟨Msrc, hMsrc, hClose⟩ :=
    actual_Hartree_moment_locked_speed_profiles_uniform_close
  obtain ⟨Cg, hCg, hGrowth⟩ := actual_Hartree_moment_locked_response_moment_growth
  let H : ℝ := (D + 1) * G
  let C0 : ℝ := 1 + H * B ^ 2
  let Dg : ℝ := 2 * Cg
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hDg : 0 ≤ Dg := by dsimp [Dg]; positivity
  let K0 : ℝ := C0 * (1 + 2 * B ^ 2 + Dg) + 4 * H * Dg
  let L0 : ℝ := 3 + 32 * K0 / B ^ 2 + 1 / B
  let epsilon : ℝ := B ^ 2 / (32 * (C0 * Msrc * B ^ 3 + 1))
  have hRegion := actual_coupled_explicit_small_parameter_region
    C0 H Msrc Dg B hC0 hH hMsrc.le hDg hB
  have hL0 : 3 ≤ L0 := hRegion.1
  have hepsilon : 0 < epsilon := hRegion.2.1
  refine ⟨L0, epsilon, hL0, hepsilon, ?_⟩
  intro L c a hLp hLarge ha hc hSmall
  have hLone : 1 ≤ L := by linarith
  have hLtwo : 2 < L := by linarith
  have hapos : 0 < a := lt_of_lt_of_le (pow_pos hLp 3) ha
  have hData := hGrowth L c hLone hc
  dsimp only at hData
  have hMoment : actualMomentLockedResponseMomentSum L c hLp ≤ Dg * L ^ 4 := by
    calc
      _ ≤ Cg * L ^ 4 + Cg * L ^ 4 :=
        add_le_add hData.2.2.2.1 hData.2.2.2.2
      _ = Dg * L ^ 4 := by dsimp [Dg]; ring
  have hCharge : actualMomentLockedResponseChargeSum L c ≤ Dg * L ^ 4 := by
    calc
      _ ≤ Cg * L ^ 4 + Cg * L ^ 4 :=
        add_le_add hData.2.1.1 hData.2.1.2
      _ = Dg * L ^ 4 := by dsimp [Dg]; ring
  have hSmallBudget := hRegion.2.2 L a c
    (actualMomentLockedResponseMomentSum L c hLp)
    (actualMomentLockedResponseChargeSum L c)
    hLarge ha hSmall hMoment hCharge
  have hBudget : actualMomentLockedFullColumnBudget L c hLp a B H C0 Msrc ≤
      B ^ 2 / 16 := by
    simpa only [actualMomentLockedFullColumnBudget,
      actualMomentLockedCoupledTraceBudget, add_assoc] using hSmallBudget.2.2
  exact actual_Hartree_moment_locked_coupled_determinant_lower_bound_of_budget
    Msrc hMsrc hClose K D G hD hG hB hBR hcoeff hbound hsmallB
    L c a hLtwo hapos hSmallBudget.2.1 hBudget

end HBL.TypeIIDynamicSelection
