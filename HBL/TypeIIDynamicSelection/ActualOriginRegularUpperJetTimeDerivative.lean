import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer
import Mathlib.Tactic

/-!
# Time derivative of the compatibility-cancelled regular upper Kummer jet

After the singular mode has been killed by the true compatibility condition,
the upper Kummer value and slope are a fixed regular basis jet times a single
complex scalar coefficient gamma(s).  This file records the exact derivative
and norm estimate for that product.

This is deliberately a frozen-basis bridge.  It does NOT assert that the
actual scalar gamma(s) already has the required derivative; producing that
derivative from the moving Fredholm source, lower endpoint, and selected
Cramer speeds is the next main-chain obligation.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

def actualOriginRegularUpperValue
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B : ℝ) (gamma : ℝ → ℂ) (s : ℝ) : ℂ :=
  originPhysicalValue K.x B * gamma s

def actualOriginRegularUpperSlope
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B : ℝ) (gamma : ℝ → ℂ) (s : ℝ) : ℂ :=
  originPhysicalSlope K.x K.dx B * gamma s

theorem actual_origin_regular_upper_jet_hasDerivAt
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B : ℝ) (gamma : ℝ → ℂ) (s : ℝ) (gammaDot : ℂ)
    (hgamma : HasDerivAt gamma gammaDot s) :
    HasDerivAt (actualOriginRegularUpperValue K B gamma)
      (originPhysicalValue K.x B * gammaDot) s ∧
    HasDerivAt (actualOriginRegularUpperSlope K B gamma)
      (originPhysicalSlope K.x K.dx B * gammaDot) s := by
  constructor
  · let c : ℂ := originPhysicalValue K.x B
    have heq :
        actualOriginRegularUpperValue K B gamma =
          (fun t => gamma t * c) := by
      funext t
      dsimp [actualOriginRegularUpperValue, c]
      rw [mul_comm]
    rw [heq]
    simpa only [c, mul_comm] using hgamma.mul_const c
  · let c : ℂ := originPhysicalSlope K.x K.dx B
    have heq :
        actualOriginRegularUpperSlope K B gamma =
          (fun t => gamma t * c) := by
      funext t
      dsimp [actualOriginRegularUpperSlope, c]
      rw [mul_comm]
    rw [heq]
    simpa only [c, mul_comm] using hgamma.mul_const c

theorem actual_origin_regular_upper_jet_derivative_norm_exact
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B : ℝ) (gamma : ℝ → ℂ) (s : ℝ) (gammaDot : ℂ)
    (hgamma : HasDerivAt gamma gammaDot s) :
    ‖deriv (actualOriginRegularUpperValue K B gamma) s‖ +
        B * ‖deriv (actualOriginRegularUpperSlope K B gamma) s‖ =
      (‖originPhysicalValue K.x B‖ +
        B * ‖originPhysicalSlope K.x K.dx B‖) * ‖gammaDot‖ := by
  have hd :=
    actual_origin_regular_upper_jet_hasDerivAt K B gamma s gammaDot hgamma
  rw [hd.1.deriv, hd.2.deriv, norm_mul, norm_mul]
  ring

theorem actual_origin_regular_upper_jet_derivative_norm_le
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B Cv Cs : ℝ) (hB : 0 ≤ B) (_hCv : 0 ≤ Cv) (_hCs : 0 ≤ Cs)
    (hValue : ‖originPhysicalValue K.x B‖ ≤ Cv)
    (hSlope : ‖originPhysicalSlope K.x K.dx B‖ ≤ Cs)
    (gamma : ℝ → ℂ) (s : ℝ) (gammaDot : ℂ)
    (hgamma : HasDerivAt gamma gammaDot s) :
    ‖deriv (actualOriginRegularUpperValue K B gamma) s‖ +
        B * ‖deriv (actualOriginRegularUpperSlope K B gamma) s‖ ≤
      (Cv + B * Cs) * ‖gammaDot‖ := by
  rw [actual_origin_regular_upper_jet_derivative_norm_exact
    K B gamma s gammaDot hgamma]
  have hbasis :
      ‖originPhysicalValue K.x B‖ +
          B * ‖originPhysicalSlope K.x K.dx B‖ ≤
        Cv + B * Cs :=
    add_le_add hValue (mul_le_mul_of_nonneg_left hSlope hB)
  exact mul_le_mul_of_nonneg_right hbasis (norm_nonneg gammaDot)

end HBL.TypeIIDynamicSelection
