import HBL.TypeIIDynamicSelection.ActualHartreeBackwardMatchedValueGain
import HBL.TypeIIDynamicSelection.ActualHartreeShellWeightedNorm
import HBL.TypeIIDynamicSelection.ActualHartreeBackwardShellRegion
import Mathlib.Tactic

/-!
# Spectral FIRST-ORDER source in the ORIGINAL Hartree radial-conjugated norm

For the ORIGINAL unshifted physical Kummer operator, the genuine matched
spectral correction leaves -a^{-2} delta*u0, not the quadratic defect of
the artificially shifted operator. Here the actual original matched
Kummer field u0 is bounded on the backward shell using its TWO genuine
weighted Fredholm source channels, without any independent amplitude
majorant. The full r-conjugation, 7/4 weight, and shell volume are
retained and a >= (2R)^3 converts the geometric radius loss to R^(-3/4).

The same-source equation and Cauchy matching are explicit hypotheses
produced by the separate original physical Hartree plateau theorem; the
only separate analytic regularity is measurability of the field.
This theorem does not assert a time-positive s-power or complete four
region nonlinear Hartree PDE residual.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.Profile.Kummer HBL.L2Kernel

/-- First-order spectral forcing -a^-2 delta*u0 in the original
conjugated Hartree source norm, with NO arbitrary value envelope. -/
theorem actual_Hartree_backward_spectral_first_order_shell_source_gain
    (mu theta a R r0 : ℝ)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (domain : Set ℝ) (v : ℝ → ℂ) (delta : ℂ)
    (hcp : Continuous Fp) (hcm : Continuous Fm)
    (hDomain : IsOpen domain) (hSub : Icc R (2 * R) ⊆ domain)
    (ha : 0 < a) (hR : 2 < R)
    (hCubic : (2 * R) ^ 3 ≤ a)
    (hSmall : 16 * R ^ 2 *
      ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1)
    (hr0 : r0 ∈ Icc R (2 * R))
    (hv : ∀ x ∈ domain, DifferentiableAt ℝ v x)
    (hv2 : ∀ x ∈ Icc R (2 * R),
      DifferentiableAt ℝ (deriv v) x)
    (hMeas : Measurable v)
    (hLeft : actualHartreeTwoChannelInner Fp Fm hp hm r0 = v r0)
    (hDerivLeft :
      deriv (actualHartreeTwoChannelInner Fp Fm hp hm) r0 = deriv v r0)
    (hSame : ∀ x ∈ Icc R (2 * R),
      actualMatchedScaledKummerApply mu theta a v x =
        -actualHartreeTwoChannelPhysicalSource Fp Fm x) :
    let N := innerWeightedNorm (7 / 4 : ℝ) Fp +
      innerWeightedNorm (7 / 4 : ℝ) Fm
    let A := actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
    let D := actualInnerShellValueConstant * N + 8 * R ^ 2 * A
    let E : ℝ → ℂ := fun y => ((a ^ 2)⁻¹ : ℝ) • (delta * v y)
    InWeightedL2 (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ∧
      innerWeightedNorm (7 / 4 : ℝ)
        (actualConjugatedShellMagnitude R E) ≤
          20 * (‖delta‖ * D) * R ^ (-(3 / 4 : ℝ)) := by
  dsimp only
  let N := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let A := actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
  let D := actualInnerShellValueConstant * N + 8 * R ^ 2 * A
  let E : ℝ → ℂ := fun y => ((a ^ 2)⁻¹ : ℝ) • (delta * v y)
  let S : ℝ := (a ^ 2)⁻¹ * ‖delta‖ * D
  have hRpos : 0 < R := by linarith
  have hRone : 1 ≤ R := by linarith
  have hRin : R ∈ Icc R (2 * R) := by
    constructor
    · exact le_rfl
    · linarith
  have hV := actual_Hartree_backward_original_matched_Kummer_value_from_same_source
    mu theta a R r0 Fp Fm hp hm domain v
    hcp hcm hDomain hSub ha hR hSmall hr0
    hv hv2 hLeft hDerivLeft hSame
  have hD : 0 ≤ D := by
    have hBound := hV R hRin
    change ‖v R‖ ≤ D at hBound
    exact (norm_nonneg _).trans hBound
  have hInv : 0 ≤ (a ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg a)
  have hCoef : 0 ≤ (a ^ 2)⁻¹ * ‖delta‖ :=
    mul_nonneg hInv (norm_nonneg delta)
  have hS : 0 ≤ S := mul_nonneg hCoef hD
  have hPoint (y : ℝ) (hy : y ∈ Icc R (2 * R)) :
      ‖E y‖ ≤ S := by
    have hValue := hV y hy
    change ‖v y‖ ≤ D at hValue
    have heq : ‖E y‖ = ((a ^ 2)⁻¹ * ‖delta‖) * ‖v y‖ := by
      dsimp only [E]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hInv,
        norm_mul]
    calc
      ‖E y‖ = ((a ^ 2)⁻¹ * ‖delta‖) * ‖v y‖ := heq
      _ ≤ ((a ^ 2)⁻¹ * ‖delta‖) * D :=
        mul_le_mul_of_nonneg_left hValue hCoef
      _ = S := rfl
  have hEMeas : Measurable E := by
    dsimp [E]
    exact (measurable_const.smul (measurable_const.mul hMeas))
  have hShell :=
    actual_conjugated_shell_weighted_power_bound
      R S hRone hS E hEMeas hPoint
  have hScale :
      (‖delta‖ * D) * R ^ (13 / 4 : ℝ) / a ^ 2 ≤
        (‖delta‖ * D) * R ^ (-(3 / 4 : ℝ)) := by
    have hFactor := actual_Hartree_backward_shell_relative_factor
      (2 * R) a 0 (‖delta‖ * D)
      (by linarith : 2 ≤ 2 * R)
      hCubic
      (mul_nonneg (norm_nonneg delta) hD)
    have hTwo : (2 * R) / 2 = R := by ring
    simpa only [hTwo, zero_mul, zero_add] using hFactor
  refine ⟨hShell.1, ?_⟩
  calc
    innerWeightedNorm (7 / 4 : ℝ)
        (actualConjugatedShellMagnitude R E) ≤
      20 * R ^ (13 / 4 : ℝ) * S := hShell.2
    _ = 20 * ((‖delta‖ * D) * R ^ (13 / 4 : ℝ) / a ^ 2) := by
      dsimp [S]
      ring
    _ ≤ 20 * ((‖delta‖ * D) * R ^ (-(3 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hScale (by norm_num)
    _ = 20 * (‖delta‖ * D) * R ^ (-(3 / 4 : ℝ)) := by ring

end HBL.TypeIIDynamicSelection
