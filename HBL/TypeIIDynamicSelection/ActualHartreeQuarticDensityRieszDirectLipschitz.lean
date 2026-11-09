import HBL.TypeIIDynamicSelection.ActualHartreeQuarticDensityDirectLipschitz
import HBL.TypeIIDynamicSelection.ActualHartreeBubbleSquaredDominatedRieszSpatialDecay
import Mathlib.Tactic

/-!
# Original nonlocal Hartree quartic-density Taylor Riesz direct Lipschitz

For the SAME physical complex background U, two genuine corrections H1,H2
have a quadratic Taylor density source difference whose actual original
inverse-square radial Riesz potential is Lipschitz. No differentiation in
threshold parameters and no independent nonlocal-source Lipschitz bound.

The bound is pointwise in the Riesz output r; connection to the full
moving four-piece Hartree residual and its weighted norm is separate.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_quartic_density_Riesz_direct_Lipschitz
    (U H1 H2 : ℝ → ℂ)
    (hUmeas : Measurable U)
    (hH1meas : Measurable H1)
    (hH2meas : Measurable H2)
    (M e d : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e) (hd : 0 ≤ d)
    (hU : ∀ x : ℝ, 0 < x → ‖U x‖ ≤ M)
    (hH1 : ∀ x : ℝ, 0 < x → ‖H1 x‖ ≤ e*bubble x)
    (hH2 : ∀ x : ℝ, 0 < x → ‖H2 x‖ ≤ e*bubble x)
    (hD : ∀ x : ℝ, 0 < x → ‖H1 x-H2 x‖ ≤ d*bubble x)
    (r : ℝ) (hr : 0 < r) :
    let F : ℝ → ℝ := fun x =>
      actualHartreeComplexDensityRemainder (U x) (H1 x) -
        actualHartreeComplexDensityRemainder (U x) (H2 x)
    let C : ℝ := (12*M^2*e + 12*M*e^2 + 4*e^3)*d
    IntegrableOn (fun x => x*hartreeRadialLog r x*F x) (Ioi (0:ℝ)) ∧
    |radialHartreePotential F r| ≤
      C*actualHartreeBubbleSquaredRieszDecayConstant/(1+r) := by
  dsimp only
  let F : ℝ → ℝ := fun x =>
    actualHartreeComplexDensityRemainder (U x) (H1 x) -
      actualHartreeComplexDensityRemainder (U x) (H2 x)
  let C : ℝ := (12*M^2*e + 12*M*e^2 + 4*e^3)*d
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hFmeas : Measurable F := by
    dsimp [F, actualHartreeComplexDensityRemainder,
      actualHartreeComplexRealPair]
    fun_prop
  have hFbound (x : ℝ) (hx : 0 < x) :
      |F x| ≤ C*bubble x^2 := by
    let W : ℝ := bubble x
    have hW : 0 ≤ W := bubble_nonneg x
    have hW1 : W ≤ 1 := bubble_le_one x
    have hW2 : W^2 ≤ 1 := by
      exact (pow_le_pow_left₀ hW hW1 2).trans_eq (by ring)
    have hCurrent :=
      actual_Hartree_quartic_density_remainder_direct_Lipschitz
        (U x) (H1 x) (H2 x) M (e*W) (d*W)
        hM (mul_nonneg he hW) (mul_nonneg hd hW)
        (hU x hx) (hH1 x hx) (hH2 x hx) (hD x hx)
    have hCoef :
        12*M^2*e + 12*M*e^2*W + 4*e^3*W^2 ≤
        12*M^2*e + 12*M*e^2 + 4*e^3 := by
      have h1 : 12*M*e^2*W ≤ 12*M*e^2 := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hW1
            (show (0 : ℝ) ≤ 12*M*e^2 by positivity))
      have h2 : 4*e^3*W^2 ≤ 4*e^3 := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hW2
            (show (0 : ℝ) ≤ 4*e^3 by positivity))
      linarith
    calc
      |F x| ≤
          (12*M^2*(e*W) + 12*M*(e*W)^2 + 4*(e*W)^3)*(d*W) :=
        hCurrent
      _ = (12*M^2*e + 12*M*e^2*W + 4*e^3*W^2)*(d*W^2) := by ring
      _ ≤ (12*M^2*e + 12*M*e^2 + 4*e^3)*(d*W^2) :=
        mul_le_mul_of_nonneg_right hCoef
          (mul_nonneg hd (sq_nonneg W))
      _ = C*bubble x^2 := by dsimp [C,W]; ring
  have hMain :=
    actual_Hartree_true_Riesz_bubble_squared_dominated_spatial_decay
      F hFmeas C hC hFbound r hr
  simpa only [F,C] using hMain

end HBL.TypeIIDynamicSelection
