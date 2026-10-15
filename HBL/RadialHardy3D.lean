import HBL.HilbertTestRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Three-dimensional radial Hardy estimate used by the first manuscript lemma.

For a radial three-dimensional profile, after removing the common spherical
factor, the homogeneous energy density is `r^2 |f'(r)|^2`.  This file proves
the exact one-dimensional Hardy estimate needed to control compactly supported
threshold tests.  The proof is the standard integration-by-parts and square
completion argument.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace HBL.Modulation

/-- Three-dimensional radial Hardy inequality on a finite interval, with the
outer Dirichlet condition appropriate for compactly supported radial cores. -/
theorem radialHardy3D (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hfR : f R = 0) :
    (∫ r in (0 : ℝ)..R, (f r) ^ 2) ≤
      4 * (∫ r in (0 : ℝ)..R, r ^ 2 * (deriv f r) ^ 2) := by
  let A : ℝ → ℝ := fun r => (f r) ^ 2
  let B : ℝ → ℝ := fun r => r ^ 2 * (deriv f r) ^ 2
  let C : ℝ → ℝ := fun r => r * f r * deriv f r
  let J : ℝ → ℝ := fun r => r * (f r) ^ 2
  have hfd : Continuous (deriv f) := hf.continuous_deriv_one
  have hA : Continuous A := by
    dsimp [A]
    fun_prop
  have hB : Continuous B := by
    dsimp [B]
    fun_prop
  have hC : Continuous C := by
    dsimp [C]
    fun_prop
  have hAi := hA.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hBi := hB.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hCi := hC.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hder (r : ℝ) :
      HasDerivAt J (A r + 2 * C r) r := by
    have h :=
      (hasDerivAt_id r).mul
        (((hf.differentiable (by norm_num) r).hasDerivAt).pow 2)
    apply h.congr_deriv
    dsimp [J, A, C]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hboundary :
      (∫ r in (0 : ℝ)..R, A r + 2 * C r) = 0 := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hder r) (hAi.add (hCi.const_mul 2))
    simpa [J, hfR] using he
  have hboundary' :
      (∫ r in (0 : ℝ)..R, A r) +
        2 * (∫ r in (0 : ℝ)..R, C r) = 0 := by
    rw [intervalIntegral.integral_add hAi (hCi.const_mul 2),
      intervalIntegral.integral_const_mul] at hboundary
    exact hboundary
  have hnonneg :
      0 ≤ ∫ r in (0 : ℝ)..R, (A r + 4 * C r) + 4 * B r := by
    apply intervalIntegral.integral_nonneg hR
    intro r _
    have hh := sq_nonneg (f r + 2 * r * deriv f r)
    dsimp [A, B, C]
    nlinarith
  rw [intervalIntegral.integral_add (hAi.add (hCi.const_mul 4))
      (hBi.const_mul 4),
    intervalIntegral.integral_add hAi (hCi.const_mul 4),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hnonneg
  change (∫ r in (0 : ℝ)..R, A r) ≤
    4 * (∫ r in (0 : ℝ)..R, B r)
  linarith

end HBL.Modulation
