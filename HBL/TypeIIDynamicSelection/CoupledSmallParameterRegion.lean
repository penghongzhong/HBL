import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
An explicit REAL-ALGEBRA parameter region for the actual coupled-column
estimate. The source and trace terms are kept separately until the last
bound. The moment/charge bounds are supplied by the fixed Fredholm response
estimates in the physical application; no matrix invertibility or small
total error is assumed here.

The small monopole term a*|c| is independent of the slow inner radius.
In particular, no condition a*|c|*L^2 <= 1, limiting rate, or upper bound
on the emergent modulation exponent is imposed by this algebraic component.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

/-- The complete relaxed source-plus-trace budget. Q denotes a bound for
the forced real affine charges, not the complex reference projection.
The estimate only needs the upper bounds for M,Q; physical nonnegativity
is available in the intended application but is unnecessary for this algebra. -/
theorem actual_coupled_error_budget_le_inverse_square
    {C0 H Ms D B L a c M Q : ℝ}
    (hC0 : 0 ≤ C0) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hL : 1 ≤ L) (ha : L ^ 3 ≤ a)
    (hM : M ≤ D * L ^ 4) (hQ : Q ≤ D * L ^ 4) :
    C0 * L ^ 2 / a ^ 2 + 2 * C0 * B ^ 2 / L ^ 2 +
        C0 * Ms * B ^ 3 * (a * |c|) + C0 * M / a ^ 2 +
        2 * H * (L ^ 3 * Q + L ^ 2 * M) / a ^ 4 ≤
      (C0 * (1 + 2 * B ^ 2 + D) + 4 * H * D) / L ^ 2 +
        C0 * Ms * B ^ 3 * (a * |c|) := by
  have hLpos : 0 < L := by linarith
  have hapos : 0 < a := lt_of_lt_of_le (pow_pos hLpos 3) ha
  have ha2 : L ^ 6 ≤ a ^ 2 := by
    simpa only [← pow_mul] using
      pow_le_pow_left₀ (pow_nonneg hLpos.le 3) ha 2
  have ha4 : L ^ 12 ≤ a ^ 4 := by
    simpa only [← pow_mul] using
      pow_le_pow_left₀ (pow_nonneg hLpos.le 3) ha 4
  have h46 : L ^ 4 ≤ L ^ 6 := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ L ^ 2 from one_le_pow₀ hL)
      (pow_nonneg hLpos.le 4)
    nlinarith only [h]
  have h912 : L ^ 9 ≤ L ^ 12 := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ L ^ 3 from one_le_pow₀ hL)
      (pow_nonneg hLpos.le 9)
    nlinarith only [h]
  have h812 : L ^ 8 ≤ L ^ 12 := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ L ^ 4 from one_le_pow₀ hL)
      (pow_nonneg hLpos.le 8)
    nlinarith only [h]
  have hRsource : L ^ 2 / a ^ 2 ≤ 1 / L ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hapos 2) (pow_pos hLpos 2)).2
    nlinarith only [h46.trans ha2]
  have hRmoment : M / a ^ 2 ≤ D / L ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hapos 2) (pow_pos hLpos 2)).2
    calc
      M * L ^ 2 ≤ (D * L ^ 4) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hM (sq_nonneg L)
      _ = D * L ^ 6 := by ring
      _ ≤ D * a ^ 2 := mul_le_mul_of_nonneg_left ha2 hD
  have hQnum : L ^ 3 * Q * L ^ 2 ≤ D * a ^ 4 := by
    calc
      _ ≤ (L ^ 3 * (D * L ^ 4)) * L ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQ (pow_nonneg hLpos.le 3)) (sq_nonneg L)
      _ = D * L ^ 9 := by ring
      _ ≤ D * L ^ 12 := mul_le_mul_of_nonneg_left h912 hD
      _ ≤ D * a ^ 4 := mul_le_mul_of_nonneg_left ha4 hD
  have hMnum : L ^ 2 * M * L ^ 2 ≤ D * a ^ 4 := by
    calc
      _ ≤ (L ^ 2 * (D * L ^ 4)) * L ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hM (sq_nonneg L)) (sq_nonneg L)
      _ = D * L ^ 8 := by ring
      _ ≤ D * L ^ 12 := mul_le_mul_of_nonneg_left h812 hD
      _ ≤ D * a ^ 4 := mul_le_mul_of_nonneg_left ha4 hD
  have hRtrace : (L ^ 3 * Q + L ^ 2 * M) / a ^ 4 ≤ (2 * D) / L ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hapos 4) (pow_pos hLpos 2)).2
    nlinarith only [hQnum, hMnum]
  have hSource : C0 * L ^ 2 / a ^ 2 ≤ C0 / L ^ 2 := by
    calc
      _ = C0 * (L ^ 2 / a ^ 2) := by ring
      _ ≤ C0 * (1 / L ^ 2) := mul_le_mul_of_nonneg_left hRsource hC0
      _ = C0 / L ^ 2 := by ring
  have hMoment : C0 * M / a ^ 2 ≤ C0 * D / L ^ 2 := by
    calc
      _ = C0 * (M / a ^ 2) := by ring
      _ ≤ C0 * (D / L ^ 2) := mul_le_mul_of_nonneg_left hRmoment hC0
      _ = C0 * D / L ^ 2 := by ring
  have hTrace : 2 * H * (L ^ 3 * Q + L ^ 2 * M) / a ^ 4 ≤
      4 * H * D / L ^ 2 := by
    calc
      _ = (2 * H) * ((L ^ 3 * Q + L ^ 2 * M) / a ^ 4) := by ring
      _ ≤ (2 * H) * ((2 * D) / L ^ 2) :=
        mul_le_mul_of_nonneg_left hRtrace (by positivity)
      _ = 4 * H * D / L ^ 2 := by ring
  calc
    _ ≤ C0 / L ^ 2 + 2 * C0 * B ^ 2 / L ^ 2 +
        C0 * Ms * B ^ 3 * (a * |c|) + C0 * D / L ^ 2 +
        4 * H * D / L ^ 2 := by linarith only [hSource, hMoment, hTrace]
    _ = _ := by ring

/-- Explicit constants give a nonempty small-parameter region, without a
small-total-error hypothesis. The true physical application must establish
the displayed scale/moment/charge bounds for its actual trajectory. -/
theorem actual_coupled_explicit_small_parameter_region
    (C0 H Ms D B : ℝ)
    (hC0 : 0 ≤ C0) (hH : 0 ≤ H) (hMs : 0 ≤ Ms) (hD : 0 ≤ D) (hB : 0 < B) :
    let K := C0 * (1 + 2 * B ^ 2 + D) + 4 * H * D
    let L0 := 3 + 32 * K / B ^ 2 + 1 / B
    let epsilon := B ^ 2 / (32 * (C0 * Ms * B ^ 3 + 1))
    3 ≤ L0 ∧ 0 < epsilon ∧
      ∀ L a c M Q : ℝ, L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
        M ≤ D * L ^ 4 → Q ≤ D * L ^ 4 →
        0 < L / a ∧ L / a ≤ B ∧
        C0 * L ^ 2 / a ^ 2 + 2 * C0 * B ^ 2 / L ^ 2 +
            C0 * Ms * B ^ 3 * (a * |c|) + C0 * M / a ^ 2 +
            2 * H * (L ^ 3 * Q + L ^ 2 * M) / a ^ 4 ≤ B ^ 2 / 16 := by
  let K : ℝ := C0 * (1 + 2 * B ^ 2 + D) + 4 * H * D
  let L0 : ℝ := 3 + 32 * K / B ^ 2 + 1 / B
  let T : ℝ := C0 * Ms * B ^ 3
  let epsilon : ℝ := B ^ 2 / (32 * (T + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hKterm : 0 ≤ 32 * K / B ^ 2 := by positivity
  have hInvB : 0 ≤ 1 / B := by positivity
  have hL0 : 3 ≤ L0 := by dsimp [L0]; linarith
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  refine ⟨hL0, hepsilon, ?_⟩
  intro L a c M Q hL ha hc hM hQ
  change L0 ≤ L at hL
  change a * |c| ≤ epsilon at hc
  have hLone : 1 ≤ L := by linarith [hL0]
  have hLpos : 0 < L := by linarith
  have hapos : 0 < a := lt_of_lt_of_le (pow_pos hLpos 3) ha
  have hKL : 32 * K / B ^ 2 ≤ L := by
    dsimp [L0] at hL
    linarith
  have hBL : 1 / B ≤ L := by
    dsimp [L0] at hL
    linarith
  have hLsq : L ≤ L ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hLone hLpos.le
    nlinarith only [h]
  have hL23 : L ^ 2 ≤ L ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hLone (sq_nonneg L)
    nlinarith only [h]
  have hInterface : L / a ≤ B := by
    have hFirst : L / a ≤ 1 / L := by
      apply (div_le_div_iff₀ hapos hLpos).2
      nlinarith only [hL23.trans ha]
    have hSecond : 1 / L ≤ B := by
      apply (div_le_iff₀ hLpos).2
      have h := (div_le_iff₀ hB).1 hBL
      nlinarith only [h]
    exact hFirst.trans hSecond
  have hBase : K / L ^ 2 ≤ B ^ 2 / 32 := by
    apply (div_le_iff₀ (pow_pos hLpos 2)).2
    have h1 := (div_le_iff₀ (pow_pos hB 2)).1 hKL
    have h2 := mul_le_mul_of_nonneg_left hLsq (sq_nonneg B)
    nlinarith only [h1, h2]
  have hTepsilon : T * epsilon ≤ B ^ 2 / 32 := by
    have hTpos : 0 < T + 1 := by linarith
    have hRatio : T / (T + 1) ≤ 1 := (div_le_iff₀ hTpos).2 (by linarith)
    calc
      T * epsilon = (B ^ 2 / 32) * (T / (T + 1)) := by
        dsimp [epsilon]
        field_simp [hTpos.ne'] <;> ring
      _ ≤ (B ^ 2 / 32) * 1 :=
        mul_le_mul_of_nonneg_left hRatio (by positivity)
      _ = B ^ 2 / 32 := by ring
  have hSmallSource : C0 * Ms * B ^ 3 * (a * |c|) ≤ B ^ 2 / 32 := by
    exact (mul_le_mul_of_nonneg_left hc hT).trans hTepsilon
  refine ⟨div_pos hLpos hapos, hInterface, ?_⟩
  have hBudget := actual_coupled_error_budget_le_inverse_square
    (Ms := Ms) (B := B) (c := c) hC0 hH hD hLone ha hM hQ
  calc
    _ ≤ K / L ^ 2 + C0 * Ms * B ^ 3 * (a * |c|) := hBudget
    _ ≤ B ^ 2 / 32 + B ^ 2 / 32 := add_le_add hBase hSmallSource
    _ = B ^ 2 / 16 := by ring

end HBL.TypeIIDynamicSelection
