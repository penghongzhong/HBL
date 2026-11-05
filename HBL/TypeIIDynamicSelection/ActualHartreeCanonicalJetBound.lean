import HBL.TypeIIDynamicSelection.ActualHartreeCompleteObstructionBound
import Mathlib.Tactic

/-!
# Canonical two-channel inner jet from the original weighted source norm

This exposes the left-Cauchy-jet estimate already proved internally in the
complete-obstruction analysis.  It is generic in the two real Fredholm
sources and therefore applies after the actual modulation-speed correction.

At the physical matching radius L the value is O(N), the physical
derivative is O(N/L^2), and the Kummer derivative carries the scale factor a.
Multiplication by the Kummer radius L/a cancels that factor, leaving a
uniform O(N) jet with no moving-endpoint loss.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

private theorem canonical_jet_real_pair_norm (u v : ℝ) :
    ‖(u : ℂ) + Complex.I * (v : ℂ)‖ ≤ |u| + |v| := by
  exact (norm_add_le _ _).trans_eq (by
    simp [Complex.norm_real, Real.norm_eq_abs])

/-- The actual normalized Fredholm Cauchy jet at L/a is controlled by the
same weighted source norm, uniformly in the spatial scale a. -/
theorem actual_Hartree_canonical_inner_jet_source_norm_bound
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (hcp : Continuous Fp) (hcm : Continuous Fm)
    (L a : ℝ) (hL : 2 < L) (ha : 0 < a) :
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    ‖J.1‖ + (L / a) * ‖J.2‖ ≤
      (actualInnerShellValueConstant + actualInnerShellDerivativeConstant) *
        (innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm) := by
  dsimp only
  let up := actualMomentLockedPhysicalPlus Fp hp
  let um := actualMomentLockedPhysicalMinus Fm hm
  let Np := innerWeightedNorm (7 / 4 : ℝ) Fp
  let Nm := innerWeightedNorm (7 / 4 : ℝ) Fm
  let N := Np + Nm
  let V := actualInnerShellValueConstant
  let T := actualInnerShellDerivativeConstant
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hN : 0 ≤ N := add_nonneg
    (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hV : 0 ≤ V := by
    dsimp [V, actualInnerShellValueConstant]
    positivity
  have hT : 0 ≤ T := by
    dsimp [T, actualInnerShellDerivativeConstant]
    positivity
  have hScale : a * (L / a) = L := by field_simp [ha.ne']
  have hpj :=
    (actual_Hartree_normalized_inner_shell_equation_bound
      Fp hp hcp L L hL le_rfl).1
  have hmj :=
    (actual_Hartree_normalized_inner_shell_equation_bound
      Fm hm hcm L L hL le_rfl).2
  have hpv : |up L| ≤ V * Np := hpj.1
  have hmv : |um L| ≤ V * Nm := hmj.1
  have hpFun : (fun x : ℝ =>
      normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) Fp hp x / x) = up := by
    funext x
    rfl
  have hmFun : (fun x : ℝ =>
      normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) Fm hm x / x) = um := by
    funext x
    rfl
  have hpdRaw : L ^ 2 * |deriv up L| ≤ T * Np := by
    have h := hpj.2.1
    rw [hpFun] at h
    exact h
  have hmdRaw : L ^ 2 * |deriv um L| ≤ T * Nm := by
    have h := hmj.2.1
    rw [hmFun] at h
    exact h
  have hpd : |deriv up L| ≤ T * Np / L ^ 2 :=
    (le_div_iff₀ (pow_pos hLp 2)).2 ((mul_comm _ _).trans_le hpdRaw)
  have hmd : |deriv um L| ≤ T * Nm / L ^ 2 :=
    (le_div_iff₀ (pow_pos hLp 2)).2 ((mul_comm _ _).trans_le hmdRaw)
  have hU : ‖J.1‖ ≤ V * N := by
    change ‖(up (a * (L / a)) : ℂ) +
      Complex.I * (um (a * (L / a)) : ℂ)‖ ≤ _
    rw [hScale]
    exact ((canonical_jet_real_pair_norm _ _).trans
      (add_le_add hpv hmv)).trans_eq (by dsimp [N, Np, Nm]; ring)
  have hDU : ‖J.2‖ ≤ a * T * N / L ^ 2 := by
    change ‖(a : ℂ) *
      (((deriv up (a * (L / a)) : ℝ) : ℂ) +
        Complex.I * ((deriv um (a * (L / a)) : ℝ) : ℂ))‖ ≤ _
    rw [hScale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left
      ((canonical_jet_real_pair_norm _ _).trans
        (add_le_add hpd hmd)) ha.le).trans_eq
      (by dsimp [N, Np, Nm]; ring)
  have hPull :
      (L / a) * ‖J.2‖ ≤ T * N := by
    calc
      _ ≤ (L / a) * (a * T * N / L ^ 2) :=
        mul_le_mul_of_nonneg_left hDU (div_nonneg hLp.le ha.le)
      _ = T * N / L := by field_simp [ha.ne', hLp.ne']
      _ ≤ T * N := div_le_self (mul_nonneg hT hN) hLone
  change ‖J.1‖ + (L / a) * ‖J.2‖ ≤ (V + T) * N
  calc
    _ ≤ V * N + T * N := add_le_add hU hPull
    _ = (V + T) * N := by ring

end HBL.TypeIIDynamicSelection
