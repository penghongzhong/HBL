import HBL.TypeIIDynamicSelection.ActualHartreeFixedKummerSpectralNoLeftRadiusLoss
import Mathlib.Tactic

/-!
# Original Hartree spectral correction: exact C¹ trace budget without left-radius loss

The literal second Green field is u₁ = G₀[d G₀[F]], formed with the same
origin-normalized Kummer Wronskian and same inverse-square Hartree source.

The previously verified quadratic spectral residual alone does not control the
C¹ data that must be rematched at the Fredholm/annulus interfaces. Here we
bound BOTH the value and slope of u₁ at every radius, INCLUDING both endpoints,
by E₂ |d| E₁ Q, where E₁=2 C²(b-a), E₂=2 C³(b-a).

In particular there is no explicit a⁻² in the correction to the left and
right interface jets. The original fixed-annulus OriginBasisOn constant C
remains visible and is NOT claimed uniform for a moving inner endpoint.
The actual dynamical decay of d and the compensating nonlinear C¹ repair
must still be established from the physical Hartree orbit.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- First slope of the literal corrected original Wronskian Green field,
using the same physical source for the first and second response. -/
def actualHartreeOriginalSpectralFirstCorrectedSlope
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (a b : ℝ) (F : ℝ → ℂ) (d : ℂ) (r : ℝ) : ℂ :=
  originGreenSlope K a b F r -
    originGreenSlope K a b
      (actualHartreeOriginalSpectralFirstSource K a b F d) r

/-- Exact perturbation of BOTH original Green Cauchy coordinates.
Unlike the spectral residual alone, the estimate controls the data that
must enter the actual physical C¹ matching/repair. -/
theorem actual_Hartree_original_spectral_C1_trace_no_left_radius_loss
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (a b C Q : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ Q / x ^ 2)
    (d : ℂ) (r : ℝ) (hr : r ∈ Icc a b) :
    ‖actualHartreeOriginalSpectralFirstCorrectedField K a b F d r -
      originGreenValue K a b F r‖ +
    ‖actualHartreeOriginalSpectralFirstCorrectedSlope K a b F d r -
      originGreenSlope K a b F r‖ ≤
      (2 * C ^ 3 * (b - a)) *
        (‖d‖ * ((2 * C ^ 2 * (b - a)) * Q)) := by
  let E1 : ℝ := 2 * C ^ 2 * (b - a)
  let Q1 : ℝ → ℂ := actualHartreeOriginalSpectralFirstSource K a b F d
  let M1 : ℝ := ‖d‖ * (E1 * Q)
  have hInitial (x : ℝ) (hx : x ∈ Icc a b) :
      ‖originGreenValue K a b F x‖ ≤ E1 * Q := by
    have hFull :=
      originGreen_inverse_square_value_slope_no_left_radius_loss
        K a b C Q ha hC hQ hK F hF hx
    have hn : 0 ≤ ‖originGreenSlope K a b F x‖ := norm_nonneg _
    dsimp [E1]
    linarith only [hFull, hn]
  have hM1 : 0 ≤ M1 := by dsimp [M1, E1]; positivity
  have hQ1 : ∀ x ∈ Icc a b, ‖Q1 x‖ ≤ M1 := by
    intro x hx
    dsimp [Q1, M1, actualHartreeOriginalSpectralFirstSource]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hInitial x hx) (norm_nonneg d)
  have hFull := originGreen_value_slope_norm_le
    K a b C M1 hC hM1 hK Q1 hQ1 hr
  have hValueEq :
      actualHartreeOriginalSpectralFirstCorrectedField K a b F d r -
        originGreenValue K a b F r =
      -originGreenValue K a b Q1 r := by
    dsimp [actualHartreeOriginalSpectralFirstCorrectedField, Q1]
    ring
  have hSlopeEq :
      actualHartreeOriginalSpectralFirstCorrectedSlope K a b F d r -
        originGreenSlope K a b F r =
      -originGreenSlope K a b Q1 r := by
    dsimp [actualHartreeOriginalSpectralFirstCorrectedSlope, Q1]
    ring
  rw [hValueEq, hSlopeEq, norm_neg, norm_neg]
  simpa only [M1, E1] using hFull

/-- Same true source, pair and spectral displacement: second-order PDE defect
AND first-order C¹ interface-jet change are simultaneously controlled. -/
theorem actual_Hartree_original_spectral_C1_and_residual_no_left_radius_loss
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (a b C Q : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ Q / x ^ 2)
    (d : ℂ) (r : ℝ) (hr : r ∈ Icc a b) :
    (‖actualHartreeOriginalSpectralFirstCorrectedField K a b F d r -
        originGreenValue K a b F r‖ +
      ‖actualHartreeOriginalSpectralFirstCorrectedSlope K a b F d r -
        originGreenSlope K a b F r‖ ≤
        (2 * C ^ 3 * (b - a)) *
          (‖d‖ * ((2 * C ^ 2 * (b - a)) * Q))) ∧
    (‖actualHartreeOriginalSpectralCorrectedJetResidual K a b F d r -
        F r‖ ≤
        ‖d‖ ^ 2 * (2 * C ^ 2 * (b - a)) *
          (2 * C ^ 3 * (b - a)) * Q) := by
  exact ⟨
    actual_Hartree_original_spectral_C1_trace_no_left_radius_loss
      K a b C Q ha hC hQ hK F hF d r hr,
    actual_Hartree_original_first_spectral_correction_inverse_square_no_radius_loss
      K a b C Q ha hab hC hQ hK F hF d r hr⟩

end HBL.TypeIIDynamicSelection
