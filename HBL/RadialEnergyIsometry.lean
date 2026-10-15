import HBL.HardyCoreBridge
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

/-!
The exact radial energy identity for the change of variables U f = r f.

For a smooth radial profile compactly supported before R, the half-line
Dirichlet energy of U f coincides with the weighted radial gradient
energy. This is the isometric core required to identify the real radial
homogeneous Sobolev energy with a one-dimensional Hilbert completion.

The factor 4*pi from the angular integration is common to both sides and
is intentionally omitted. This file proves the equality on the smooth
compact core, not the completion/density theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace HBL.Modulation

/-- The actual derivative of the radial conjugation `U f = r f`. -/
theorem radialU_hasDerivAt (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (r : ℝ) :
    HasDerivAt (radialU f) (f r + r * deriv f r) r := by
  have h := (hasDerivAt_id r).mul
    ((hf.differentiable (by norm_num) r).hasDerivAt)
  change HasDerivAt (fun x : ℝ => x * f x) (f r + r * deriv f r) r
  simpa only [Pi.mul_apply, id_eq, one_mul] using h

/-- Pointwise radial derivative formula; the derivative is the sum of the
profile and its weighted derivative. -/
theorem radialU_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (r : ℝ) :
    deriv (radialU f) r = f r + r * deriv f r :=
  (radialU_hasDerivAt f hf r).deriv

/-- On the compact Dirichlet core, the radial-conjugation map preserves
the exact squared homogeneous energy. -/
theorem radialU_energy_identity
    (R : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hfR : f R = 0) :
    (∫ r in (0 : ℝ)..R, (deriv (radialU f) r) ^ 2) =
      ∫ r in (0 : ℝ)..R, r ^ 2 * (deriv f r) ^ 2 := by
  let A : ℝ → ℝ := fun r => (f r + r * deriv f r) ^ 2
  let B : ℝ → ℝ := fun r => r ^ 2 * (deriv f r) ^ 2
  let J : ℝ → ℝ := fun r => r * (f r) ^ 2
  have hDf : Continuous (deriv f) := hf.continuous_deriv_one
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hB : Continuous B := by dsimp [B]; fun_prop
  have hAi := hA.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hBi := hB.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hJ (r : ℝ) :
      HasDerivAt J (A r - B r) r := by
    have h := (hasDerivAt_id r).mul
      (((hf.differentiable (by norm_num) r).hasDerivAt).pow 2)
    apply h.congr_deriv
    dsimp [J, A, B]
    ring
  have hZero : (∫ r in (0 : ℝ)..R, A r - B r) = 0 := by
    have hFt := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hJ r) (hAi.sub hBi)
    simpa [J, hfR] using hFt
  rw [intervalIntegral.integral_sub hAi hBi] at hZero
  have hEq :
      (∫ r in (0 : ℝ)..R, A r) =
        (∫ r in (0 : ℝ)..R, B r) := by
    linarith
  calc
    (∫ r in (0 : ℝ)..R, (deriv (radialU f) r) ^ 2) =
        (∫ r in (0 : ℝ)..R, A r) := by
          apply intervalIntegral.integral_congr
          intro r _
          change (deriv (radialU f) r) ^ 2 =
            (f r + r * deriv f r) ^ 2
          rw [radialU_deriv f hf r]
    _ = ∫ r in (0 : ℝ)..R, r ^ 2 * (deriv f r) ^ 2 := hEq

end HBL.Modulation
