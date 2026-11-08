import HBL.TypeIIDynamicSelection.ActualHartreeFixedKummerOneStepSpectralGain
import HBL.KummerOriginGreen.InverseSquareSourceNoLeftRadiusLoss
import Mathlib.Tactic

/-!
# One genuine Kummer spectral correction: no inverse matching radius loss

Original radial Hartree sources satisfy |F(r)| <= Q/r², not only a
uniform source-sup bound Q/a². The exact normalized Wronskian satisfies
|W_K(r)^(-1)| = r²; these cancel INSIDE the ORIGINAL Green densities.

The first original normalized Green response u0=G0[F] therefore obeys
|u0|+|u0'| <= E1*Q with E1=2*C²*(B-a), no a^-2.
For the actual spectral difference d, the SECOND original Green
response u1=G0[d*u0] obeys |u1| <= E2*|d|*E1*Q,
where E2=2*C³*(B-a). The physical frozen-spectrum differential
identity is exactly
    L_{mu,theta}(u0-u1)-F = -d*u1.
Hence the remaining actual source is bounded by |d|²*E1*E2*Q.

This gives a real quadratic spectral reduction without any artificial
source size, without an inverse left radius, and without prescribing
a Type-II rate. It is not yet the full four-piece nonlinear PDE step.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_original_first_spectral_correction_inverse_square_no_radius_loss
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (a B C Q : ℝ) (ha : 0 < a) (hab : a ≤ B)
    (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hK : OriginBasisOn K a B C)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a B, ‖F x‖ ≤ Q / x ^ 2)
    (d : ℂ) (r : ℝ) (hr : r ∈ Icc a B) :
    ‖actualHartreeOriginalSpectralCorrectedJetResidual K a B F d r -
      F r‖ ≤
      ‖d‖ ^ 2 * (2 * C ^ 2 * (B - a)) *
        (2 * C ^ 3 * (B - a)) * Q := by
  let E1 : ℝ := 2 * C ^ 2 * (B - a)
  let E2 : ℝ := 2 * C ^ 3 * (B - a)
  let Q1 : ℝ → ℂ :=
    actualHartreeOriginalSpectralFirstSource K a B F d
  let M1 : ℝ := ‖d‖ * (E1 * Q)
  have hE1 : 0 ≤ E1 := by dsimp [E1]; positivity
  have hE2 : 0 ≤ E2 := by dsimp [E2]; positivity
  have hM1 : 0 ≤ M1 := by dsimp [M1]; positivity
  have hOriginal (x : ℝ) (hx : x ∈ Icc a B) :
      ‖originGreenValue K a B F x‖ ≤ E1 * Q := by
    have hFull :=
      originGreen_inverse_square_value_slope_no_left_radius_loss
        K a B C Q ha hC hQ hK F hF hx
    have hn : 0 ≤ ‖originGreenSlope K a B F x‖ := norm_nonneg _
    dsimp [E1]
    linarith only [hFull, hn]
  have hQ1 : ∀ x ∈ Icc a B, ‖Q1 x‖ ≤ M1 := by
    intro x hx
    dsimp [Q1, M1, actualHartreeOriginalSpectralFirstSource]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hOriginal x hx) (norm_nonneg d)
  have hGreen := originGreen_value_slope_norm_le
    K a B C M1 hC hM1 hK Q1 hQ1 hr
  have hNext :
      ‖originGreenValue K a B Q1 r‖ ≤ E2 * M1 := by
    have hn : 0 ≤ ‖originGreenSlope K a B Q1 r‖ := norm_nonneg _
    dsimp [E2]
    linarith only [hGreen, hn]
  have hExact :=
    actual_Hartree_original_Kummer_first_spectral_correction_exact
      K a B F d r
  have hDifference :
      actualHartreeOriginalSpectralCorrectedJetResidual K a B F d r -
        F r = -(d * originGreenValue K a B Q1 r) := by
    rw [hExact]
    dsimp only [Q1]
    ring
  rw [hDifference, norm_neg, norm_mul]
  calc
    ‖d‖ * ‖originGreenValue K a B Q1 r‖ ≤
        ‖d‖ * (E2 * M1) :=
      mul_le_mul_of_nonneg_left hNext (norm_nonneg d)
    _ = ‖d‖ ^ 2 * E1 * E2 * Q := by
      dsimp [M1]
      ring
    _ = _ := by rfl

end HBL.TypeIIDynamicSelection
