import HBL.TypeIIDynamicSelection.ActualHartreeTwoChannelMatchedShell
import HBL.TypeIIDynamicSelection.ActualHartreeInnerShellEquation
import Mathlib.Tactic

/-!
# The ORIGINAL matched Kummer field is bounded on the backward overlap

This produces a value bound for the original Cramer-matched physical Green
continuation on the full backward shell [R,2R], including points BELOW
its matching radius. It uses the same two normalized weighted Fredholm
sources, their actual classical ODE defect, and the exact matched
source equation. No independent exterior value envelope is assumed.

This is the needed spatial producer for retaining the first-order
spectral source -delta*u0 in the original unshifted Hartree PDE.
It does not assert any time-weighted four-domain nonlinear residual.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.Profile.Kummer HBL.L2Kernel

/-- Same-source matched original physical Kummer continuation has no
hidden value envelope assumption on the backward overlap; it follows
from the genuine normalized H+/- Fredholm values and their zero-jet
mismatch equation. -/
theorem actual_Hartree_backward_original_matched_Kummer_value_from_same_source
    (mu theta a R r0 : ℝ)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (domain : Set ℝ) (v : ℝ → ℂ)
    (hcp : Continuous Fp) (hcm : Continuous Fm)
    (hDomain : IsOpen domain)
    (hSub : Icc R (2 * R) ⊆ domain)
    (ha : 0 < a) (hR : 2 < R)
    (hSmall : 16 * R ^ 2 *
      ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1)
    (hr0 : r0 ∈ Icc R (2 * R))
    (hv : ∀ x ∈ domain, DifferentiableAt ℝ v x)
    (hv2 : ∀ x ∈ Icc R (2 * R),
      DifferentiableAt ℝ (deriv v) x)
    (hLeft : actualHartreeTwoChannelInner Fp Fm hp hm r0 = v r0)
    (hDerivLeft :
      deriv (actualHartreeTwoChannelInner Fp Fm hp hm) r0 = deriv v r0)
    (hSame : ∀ x ∈ Icc R (2 * R),
      actualMatchedScaledKummerApply mu theta a v x =
        -actualHartreeTwoChannelPhysicalSource Fp Fm x)
    (r : ℝ) (hr : r ∈ Icc R (2 * R)) :
    ‖v r‖ ≤
      actualInnerShellValueConstant *
        (innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm) +
      8 * R ^ 2 * actualHartreeTwoChannelShellBudget
        mu theta a R Fp Fm := by
  let u := actualHartreeTwoChannelInner Fp Fm hp hm
  let d : ℝ → ℂ := fun x => u x - v x
  let Np := innerWeightedNorm (7 / 4 : ℝ) Fp
  let Nm := innerWeightedNorm (7 / 4 : ℝ) Fm
  let N := Np + Nm
  let A := actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
  obtain ⟨C, _hC, hShell⟩ := actual_Hartree_two_channel_matched_shell_gain
  have hDiff :
      ‖d r‖ ≤ 8 * R ^ 2 * A :=
    (hShell mu theta a R r0 Fp Fm hp hm domain v
      hcp hcm hDomain hSub ha hR hSmall hr0
      hv hv2 hLeft hDerivLeft hSame r hr).2.1
  have hpraw :=
    (actual_Hartree_normalized_inner_shell_equation_bound
      Fp hp hcp R r hR hr.1).1.1
  have hmraw :=
    (actual_Hartree_normalized_inner_shell_equation_bound
      Fm hm hcm R r hR hr.1).2.1
  have hpValue :
      |actualMomentLockedPhysicalPlus Fp hp r| ≤
        actualInnerShellValueConstant * Np := by
    change |normalizedPlusOutput (7 / 4 : ℝ)
      (by norm_num) (by norm_num) Fp hp r / r| ≤ _
    exact hpraw
  have hmValue :
      |actualMomentLockedPhysicalMinus Fm hm r| ≤
        actualInnerShellValueConstant * Nm := by
    change |normalizedMinusOutput (7 / 4 : ℝ)
      (by norm_num) (by norm_num) Fm hm r / r| ≤ _
    exact hmraw
  have huBound : ‖u r‖ ≤ actualInnerShellValueConstant * N := by
    calc
      ‖u r‖ ≤
          ‖(actualMomentLockedPhysicalPlus Fp hp r : ℂ)‖ +
          ‖Complex.I * (actualMomentLockedPhysicalMinus Fm hm r : ℂ)‖ := by
        dsimp only [u, actualHartreeTwoChannelInner]
        exact norm_add_le _ _
      _ = |actualMomentLockedPhysicalPlus Fp hp r| +
          |actualMomentLockedPhysicalMinus Fm hm r| := by
        simp only [norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs]
      _ ≤ actualInnerShellValueConstant * Np +
          actualInnerShellValueConstant * Nm :=
        add_le_add hpValue hmValue
      _ = actualInnerShellValueConstant * N := by
        dsimp [N]
        ring
  have hvBound : ‖v r‖ ≤ ‖u r‖ + ‖d r‖ := by
    have heq : v r = u r - d r := by
      dsimp [d]
      ring
    rw [heq]
    exact norm_sub_le _ _
  exact hvBound.trans (add_le_add huBound hDiff)

end HBL.TypeIIDynamicSelection
