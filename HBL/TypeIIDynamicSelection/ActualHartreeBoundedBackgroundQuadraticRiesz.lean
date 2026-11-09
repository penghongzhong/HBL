import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylor
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# Actual inverse-square Hartree Riesz potential of the quadratic density remainder

The genuine quartic density remainder is produced from its explicit
complex polynomial. It is not an independently bounded Riesz source.
Unlike the one-bubble Taylor theorem, the entire background U is only
assumed uniformly bounded in L-infinity; its spatial decay is NOT assumed.
The perturbation H retains the bubble envelope required for the true
radial inverse-square Riesz row. The output is a REAL nonlocal potential
bound with a quadratic H factor, rather than a local surrogate.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Full original radial Hartree Riesz potential of the genuine complex
quadratic quartic-density remainder, for an arbitrary bounded background.
No global `U <= M*bubble` assumption and no assigned time gain. -/
theorem actual_Hartree_true_quadratic_density_Riesz_from_Linfty_background
    (U H : ℝ → ℂ)
    (hUmeas : Measurable U) (hHmeas : Measurable H)
    (M e : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hUB : ∀ x : ℝ, 0 < x → ‖U x‖ ≤ M)
    (hHB : ∀ x : ℝ, 0 < x → ‖H x‖ ≤ e * bubble x)
    (r : ℝ) (hr : 0 < r) :
    IntegrableOn
      (fun x => x * hartreeRadialLog r x *
        actualHartreeComplexDensityRemainder (U x) (H x))
      (Ioi (0 : ℝ)) ∧
    |radialHartreePotential
      (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r| ≤
      radialHartreeRowBoundConstant *
        ((6 * M ^ 2 + 4 * M * e + e ^ 2) * e ^ 2) := by
  let C : ℝ := (6 * M ^ 2 + 4 * M * e + e ^ 2) * e ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hFmeas : Measurable
      (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) := by
    unfold actualHartreeComplexDensityRemainder actualHartreeComplexRealPair
    fun_prop
  have hFbound (x : ℝ) (hx : 0 < x) :
      |actualHartreeComplexDensityRemainder (U x) (H x)| ≤
        C * bubble x ^ 2 := by
    let W : ℝ := bubble x
    have hW0 : 0 ≤ W := bubble_nonneg x
    have hW1 : W ≤ 1 := bubble_le_one x
    have hW3 : W ^ 3 ≤ W ^ 2 := by
      calc
        W ^ 3 = W ^ 2 * W := by ring
        _ ≤ W ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hW1 (sq_nonneg W)
        _ = W ^ 2 := by ring
    have hW2 : W ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hW0 hW1 2
    have hW4 : W ^ 4 ≤ W ^ 2 := by
      calc
        W ^ 4 = W ^ 2 * W ^ 2 := by ring
        _ ≤ W ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg W)
        _ = W ^ 2 := by ring
    have hRaw :=
      (actual_Hartree_complex_Taylor_polynomial_bounds
        (U x) (H x) hM (mul_nonneg he hW0)
        (hUB x hx) (hHB x hx)).2.1
    calc
      _ ≤ 6 * M ^ 2 * (e * W) ^ 2 +
          4 * M * (e * W) ^ 3 + (e * W) ^ 4 := hRaw
      _ = 6 * M ^ 2 * e ^ 2 * W ^ 2 +
          4 * M * e ^ 3 * W ^ 3 + e ^ 4 * W ^ 4 := by ring
      _ ≤ 6 * M ^ 2 * e ^ 2 * W ^ 2 +
          4 * M * e ^ 3 * W ^ 2 + e ^ 4 * W ^ 2 := by
        exact add_le_add
          (add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hW3 (by positivity)))
          (mul_le_mul_of_nonneg_left hW4 (by positivity))
      _ = C * bubble x ^ 2 := by dsimp [C, W]; ring
  have h := radialHartreePotential_bubble_sq_domination
    (fun x => actualHartreeComplexDensityRemainder (U x) (H x))
    hFmeas hC hFbound hr
  simpa only [C] using h

end HBL.TypeIIDynamicSelection
