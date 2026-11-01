import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeMixedPositiveHalf
import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeWeightedFredholm
import Mathlib.Tactic

/-!
# Genuine physical Hartree mixed-density L² gain on the terminal one-orbit source

The full mixed quartic density F_ell = |V_c+Z_ell|⁴-|V_c|⁴-|Z_ell|⁴
has support of physical length O(ell⁻¹), pointwise size O(ell^(5/2)),
and exact L¹ gain O(ell^(3/2)), all proved in prior physical modules.

We now derive the genuine squared L² half-line integral O(ell⁴)
from the same actual density and the existing L¹ estimate. No
prescribed Type II rate, abstract source order, source mass,
or off-terminal compact-support assumption is introduced.

This is a time-terminal source bound, not full original 2.12.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.AffineTail
open HBL.Modulation.Monopole

/-- Existing exact physical upper envelope of the entire mixed quartic
density, including all complex cross terms. -/
def actualOneOrbitVcWholeMixedPointwiseEnvelope (ell : ℝ) : ℝ :=
  4 * actualOneOrbitMovingEnvelope ^ 3 * ell ^ 3 * Real.sqrt ell +
    6 * actualOneOrbitMovingEnvelope ^ 2 * ell ^ 3 +
      4 * actualOneOrbitMovingEnvelope * ell ^ 2 * Real.sqrt ell

def actualOneOrbitVcWholeMixedL2Coefficient : ℝ :=
  4 * actualOneOrbitMovingEnvelope ^ 3 +
    6 * actualOneOrbitMovingEnvelope ^ 2 +
      4 * actualOneOrbitMovingEnvelope

/-- The actual full mixed density has an L² square controlled by
its previously verified physical L¹ mass and pointwise source bound.
The L² integrability is extracted from its true compact support and
weighted Fredholm membership, rather than assumed. -/
theorem actual_one_orbit_Vc_whole_mixed_L2_square_from_L1
    (ell : ℝ) (hell : 0 < ell) :
    (∫ r in Ioi (0 : ℝ),
      |actualOneOrbitVcWholeMixedQuartic ell r| ^ 2) ≤
      actualOneOrbitVcWholeMixedPointwiseEnvelope ell *
        actualOneOrbitVcWholeMixedL1Envelope ell := by
  let F : ℝ → ℝ := actualOneOrbitVcWholeMixedQuartic ell
  let C : ℝ := actualOneOrbitVcWholeMixedPointwiseEnvelope ell
  have hC : 0 ≤ C := by
    dsimp [C, actualOneOrbitVcWholeMixedPointwiseEnvelope]
    have hB := actual_one_orbit_moving_envelope_pos
    positivity
  have hSource :=
    actual_one_orbit_Vc_whole_mixed_Hartree_L1_center_gain ell hell
  have hWeighted : InWeightedL2 0 F :=
    actual_one_orbit_Vc_whole_mixed_in_real_weighted_Fredholm
      ell 0 hell
  have hMem : MemLp F 2 halfLineMeasure := by
    simpa [InWeightedL2, affineJapaneseWeight] using hWeighted
  have hMeas : AEStronglyMeasurable F halfLineMeasure :=
    (actual_one_orbit_Vc_whole_mixed_measurable ell).aestronglyMeasurable.restrict
  have hSq :
      IntegrableOn (fun r : ℝ => F r ^ 2) (Ioi (0 : ℝ)) :=
    (memLp_two_iff_integrable_sq hMeas).1 hMem
  have hAbsSq :
      IntegrableOn (fun r : ℝ => |F r| ^ 2) (Ioi (0 : ℝ)) := by
    simpa only [sq_abs] using hSq
  have hAbs : IntegrableOn (fun r : ℝ => |F r|) (Ioi (0 : ℝ)) :=
    hSource.1.abs.integrableOn
  have hBound : ∀ᵐ r : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      |F r| ^ 2 ≤ C * |F r| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hP := actual_one_orbit_Vc_whole_mixed_pointwise_gain
      ell r hell hr
    change |F r| ≤ C at hP
    nlinarith [mul_nonneg (abs_nonneg (F r)) (sub_nonneg.mpr hP)]
  have hMain :
      (∫ r in Ioi (0 : ℝ), |F r| ^ 2) ≤
        C * (∫ r in Ioi (0 : ℝ), |F r|) := by
    calc
      _ ≤ ∫ r in Ioi (0 : ℝ), C * |F r| :=
        integral_mono_ae hAbsSq (hAbs.const_mul C) hBound
      _ = C * (∫ r in Ioi (0 : ℝ), |F r|) := by
        rw [integral_const_mul]
  exact hMain.trans (mul_le_mul_of_nonneg_left hSource.2.1 hC)

/-- Pointwise source size O(ell^(5/2)) for 0<ell<=1,
with an explicit constant fixed by the real Hartree terminal datum. -/
theorem actual_one_orbit_Vc_whole_mixed_pointwise_five_halves
    (ell : ℝ) (hell : 0 < ell) (hsmall : ell ≤ 1) :
    actualOneOrbitVcWholeMixedPointwiseEnvelope ell ≤
      actualOneOrbitVcWholeMixedL2Coefficient *
        ell ^ 2 * Real.sqrt ell := by
  let B : ℝ := actualOneOrbitMovingEnvelope
  have hB : 0 < B := actual_one_orbit_moving_envelope_pos
  have hCub : ell ^ 3 ≤ ell ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ell) (sub_nonneg.mpr hsmall)]
  have hSqrt : ell ≤ Real.sqrt ell := by
    calc
      ell = Real.sqrt (ell ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hell]
      _ ≤ Real.sqrt ell := Real.sqrt_le_sqrt (by
        nlinarith [mul_nonneg hell.le (sub_nonneg.mpr hsmall)])
  have hCubSqrt :
      ell ^ 3 * Real.sqrt ell ≤ ell ^ 2 * Real.sqrt ell :=
    mul_le_mul_of_nonneg_right hCub (Real.sqrt_nonneg ell)
  have hCubSqrt' : ell ^ 3 ≤ ell ^ 2 * Real.sqrt ell := by
    nlinarith [mul_le_mul_of_nonneg_left hSqrt (sq_nonneg ell)]
  calc
    actualOneOrbitVcWholeMixedPointwiseEnvelope ell =
        (4 * B ^ 3) * (ell ^ 3 * Real.sqrt ell) +
          (6 * B ^ 2) * ell ^ 3 +
            (4 * B) * (ell ^ 2 * Real.sqrt ell) := by
      dsimp [actualOneOrbitVcWholeMixedPointwiseEnvelope, B]
      ring
    _ ≤ (4 * B ^ 3) * (ell ^ 2 * Real.sqrt ell) +
          (6 * B ^ 2) * (ell ^ 2 * Real.sqrt ell) +
            (4 * B) * (ell ^ 2 * Real.sqrt ell) :=
      add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hCubSqrt (by positivity))
          (mul_le_mul_of_nonneg_left hCubSqrt' (by positivity)))
        (le_refl _)
    _ = actualOneOrbitVcWholeMixedL2Coefficient *
        ell ^ 2 * Real.sqrt ell := by
      dsimp [actualOneOrbitVcWholeMixedL2Coefficient, B]
      ring

/-- Genuine physical radial squared L² gain O(ell⁴). This strengthens
mere membership in the Fredholm source space, without imposing an
artificial spatial source or postulating a blowup exponent. -/
theorem actual_one_orbit_Vc_whole_mixed_L2_square_fourth_order
    (ell : ℝ) (hell : 0 < ell) (hsmall : ell ≤ 1) :
    (∫ r in Ioi (0 : ℝ),
      |actualOneOrbitVcWholeMixedQuartic ell r| ^ 2) ≤
      (actualOneOrbitVcWholeMixedL2Coefficient *
        actualOneOrbitVcWholeMixedHalfOrderCoefficient) * ell ^ 4 := by
  have hSq :=
    actual_one_orbit_Vc_whole_mixed_L2_square_from_L1 ell hell
  have hP :=
    actual_one_orbit_Vc_whole_mixed_pointwise_five_halves
      ell hell hsmall
  have hE :=
    actual_one_orbit_Vc_whole_mixed_envelope_half_order
      ell hell hsmall
  have hEpos : 0 ≤ actualOneOrbitVcWholeMixedL1Envelope ell := by
    unfold actualOneOrbitVcWholeMixedL1Envelope
    have hB := actual_one_orbit_moving_envelope_pos
    positivity
  have hCoefPos : 0 ≤ actualOneOrbitVcWholeMixedL2Coefficient := by
    unfold actualOneOrbitVcWholeMixedL2Coefficient
    have hB := actual_one_orbit_moving_envelope_pos
    positivity
  calc
    _ ≤ actualOneOrbitVcWholeMixedPointwiseEnvelope ell *
        actualOneOrbitVcWholeMixedL1Envelope ell := hSq
    _ ≤ (actualOneOrbitVcWholeMixedL2Coefficient *
          ell ^ 2 * Real.sqrt ell) *
        actualOneOrbitVcWholeMixedL1Envelope ell :=
      mul_le_mul_of_nonneg_right hP hEpos
    _ ≤ (actualOneOrbitVcWholeMixedL2Coefficient *
          ell ^ 2 * Real.sqrt ell) *
        (actualOneOrbitVcWholeMixedHalfOrderCoefficient *
          ell * Real.sqrt ell) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = (actualOneOrbitVcWholeMixedL2Coefficient *
          actualOneOrbitVcWholeMixedHalfOrderCoefficient) * ell ^ 4 := by
      calc
        _ = (actualOneOrbitVcWholeMixedL2Coefficient *
              actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
              ell ^ 3 * (Real.sqrt ell) ^ 2 := by ring
        _ = (actualOneOrbitVcWholeMixedL2Coefficient *
              actualOneOrbitVcWholeMixedHalfOrderCoefficient) * ell ^ 4 := by
          rw [Real.sq_sqrt hell.le]
          ring

end HBL.TypeIIDynamicSelection
