import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedNondegenerateRegion
import HBL.KummerOriginBasis.Existence
import HBL.KummerOriginBasis.UniformBound

/-!
Constructed nondegeneracy of the complete moment-locked compatibility matrix.
For each frozen pair of real Kummer parameters, the origin-normalized basis
is constructed from the actual IVPs on [0,1]. Its coefficient and solution
bounds are derived, a small positive matching radius is chosen, and the
actual Fredholm-response parameter region is then instantiated. No basis
existence, coefficient bound, solution bound, or nonvanishing projection
is left as an assumption. This theorem makes no trajectory or time claim.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- For arbitrary fixed real Kummer parameters, construct the actual basis
and a positive parameter region on which the full physical matrix has a
quantitative positive determinant. -/
theorem actual_Hartree_moment_locked_constructed_nondegeneracy
    (mu theta : ℝ) :
    ∃ (K : OriginKummerPair mu theta 1) (B L0 epsilon : ℝ),
      0 < B ∧ B < 1 ∧ 3 ≤ L0 ∧ 0 < epsilon ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → |c| ≤ 1 → a * |c| ≤ epsilon →
        a ^ 2 * B ^ 4 / 256 ≤
          actualMomentLockedCoupledDeterminant K L c hLp a (L / a) B ∧
        0 < actualMomentLockedCoupledDeterminant K L c hLp a (L / a) B := by
  obtain ⟨K⟩ := exists_origin_kummer_pair mu theta 1 (by norm_num)
  let D : ℝ := 1 / 2 + ‖originZeroCoeff mu theta‖
  let G : ℝ := Real.exp ((D + 1) * 1)
  let H : ℝ := (D + 1) * G
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hG : 0 ≤ G := (Real.exp_pos _).le
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hcoeff : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D := by
    intro r hr
    have hFirst : ‖originFirstCoeff r‖ = r / 2 := by
      simp [originFirstCoeff, abs_of_nonneg hr.1]
    rw [hFirst]
    dsimp [D]
    linarith [hr.2]
  have hbound : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G :=
    origin_kummer_pair_bound K D hD hcoeff
  let B : ℝ := 1 / (4 * (H + 1))
  have hDen : 0 < 4 * (H + 1) := by positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hBOne : B < 1 := by
    dsimp [B]
    apply (div_lt_iff₀ hDen).2
    linarith
  have hHB : (H + 1) * B = 1 / 4 := by
    dsimp [B]
    field_simp [show H + 1 ≠ 0 by positivity]
  have hHBSq : (H + 1) * B ^ 2 = B / 4 := by
    calc
      _ = ((H + 1) * B) * B := by ring
      _ = B / 4 := by rw [hHB]; ring
  have hSmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1 := by
    calc
      _ = (H + 1 / 4) * B ^ 2 := rfl
      _ ≤ (H + 1) * B ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg B)
      _ = B / 4 := hHBSq
      _ ≤ 1 := by linarith
  obtain ⟨L0, epsilon, hL0, hepsilon, hRegion⟩ :=
    actual_Hartree_moment_locked_coupled_nondegenerate_region
      K D G hD hG hB hBOne hcoeff hbound hSmallB
  exact ⟨K, B, L0, epsilon, hB, hBOne, hL0, hepsilon, hRegion⟩

end HBL.TypeIIDynamicSelection
