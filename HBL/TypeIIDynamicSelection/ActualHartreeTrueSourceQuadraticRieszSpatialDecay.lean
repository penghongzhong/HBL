import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylor
import HBL.TypeIIDynamicSelection.ActualHartreeBubbleSquaredDominatedRieszSpatialDecay
import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleMeasurable
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# Spatially decaying true Hartree quadratic Riesz Taylor source

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
theorem actual_Hartree_quadratic_density_Riesz_spatial_decay_from_Linfty
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
      ((6 * M ^ 2 + 4 * M * e + e ^ 2) * e ^ 2) *
        actualHartreeBubbleSquaredRieszDecayConstant / (1 + r) := by
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
  have h := actual_Hartree_true_Riesz_bubble_squared_dominated_spatial_decay
    (fun x => actualHartreeComplexDensityRemainder (U x) (H x))
    hFmeas C hC hFbound hr
  simpa only [C] using h


theorem actual_Hartree_true_monopole_radiation_quadratic_density_Riesz_spatial_decay
    (ell c B e : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hc : |c| ≤ 1) (hB : 0 ≤ B) (he : 0 ≤ e)
    (z H : ℝ → ℂ)
    (hz : Measurable z) (hHmeas : Measurable H)
    (hSup : ∀ x : ℝ, 0 < x → ‖z x‖ ≤ B)
    (hH : ∀ x : ℝ, 0 < x → ‖H x‖ ≤ e * bubble x)
    (r : ℝ) (hr : 0 < r) :
    let U : ℝ → ℂ := fun x =>
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c x : ℂ) +
        rescalePhysicalRadiation ell z x
    let M : ℝ := 1 + monopoleRadialBoundConstant + B
    IntegrableOn
      (fun x => x * hartreeRadialLog r x *
        actualHartreeComplexDensityRemainder (U x) (H x))
      (Ioi (0 : ℝ)) ∧
    |radialHartreePotential
      (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r| ≤
      ((6 * M ^ 2 + 4 * M * e + e ^ 2) * e ^ 2) *
        actualHartreeBubbleSquaredRieszDecayConstant / (1 + r) := by
  dsimp only
  let U : ℝ → ℂ := fun x =>
    (monopolePerturbedRadialProfile
       (monopoleQuadraticRadius c) c x : ℂ) +
       rescalePhysicalRadiation ell z x
  let M : ℝ := 1 + monopoleRadialBoundConstant + B
  have hM : 0 ≤ M := by
    dsimp [M]
    have hmon := monopoleRadialBoundConstant_pos
    positivity
  have hSqrt : 0 ≤ Real.sqrt ell := Real.sqrt_nonneg ell
  have hSqrtOne : Real.sqrt ell ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hellOne
  have hVmeas :=
    actual_Hartree_moving_monopole_measurable c
  have hUmeas : Measurable U := by
    dsimp [U, rescalePhysicalRadiation]
    fun_prop
  have hUbound (x : ℝ) (hx : 0 < x) :
      ‖U x‖ ≤ M := by
    have hVbound :
        ‖(monopolePerturbedRadialProfile
            (monopoleQuadraticRadius c) c x : ℂ)‖ ≤
          1 + monopoleRadialBoundConstant := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (monopolePerturbedRadialProfile_abs_le
          (R := monopoleQuadraticRadius c) hx hc)
    have hZbound : ‖rescalePhysicalRadiation ell z x‖ ≤ B := by
      have hnorm :
          ‖rescalePhysicalRadiation ell z x‖ =
            Real.sqrt ell * ‖z (ell * x)‖ := by
        unfold rescalePhysicalRadiation
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hSqrt]
      calc
        ‖rescalePhysicalRadiation ell z x‖ =
          Real.sqrt ell * ‖z (ell * x)‖ := hnorm
        _ ≤ Real.sqrt ell * B :=
          mul_le_mul_of_nonneg_left
            (hSup (ell * x) (mul_pos hell hx)) hSqrt
        _ ≤ 1 * B :=
          mul_le_mul_of_nonneg_right hSqrtOne hB
        _ = B := one_mul B
    calc
      ‖U x‖ ≤
          ‖(monopolePerturbedRadialProfile
              (monopoleQuadraticRadius c) c x : ℂ)‖ +
          ‖rescalePhysicalRadiation ell z x‖ := norm_add_le _ _
      _ ≤ (1 + monopoleRadialBoundConstant) + B :=
        add_le_add hVbound hZbound
      _ = M := rfl
  have hMain :=
    actual_Hartree_quadratic_density_Riesz_spatial_decay_from_Linfty
      U H hUmeas hHmeas M e hM he hUbound hH r hr
  simpa only [U, M] using hMain


end HBL.TypeIIDynamicSelection
