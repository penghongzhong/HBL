import HBL.RadialEnergyIsometry

/-!
Finite-interval bilinear radial energy identity, with the boundary term
removed only under an explicit endpoint condition.  This is a core
calculation, not a Sobolev completion or a physical Hessian theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace HBL.Modulation

/-- Bilinear Dirichlet energy identity on a finite oriented radial interval. -/
theorem radialU_energy_bilinear_identity
    (R : ℝ) (f g : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hboundary : f R * g R = 0) :
    (∫ r in (0 : ℝ)..R,
      deriv (radialU f) r * deriv (radialU g) r) =
      ∫ r in (0 : ℝ)..R, r ^ 2 * deriv f r * deriv g r := by
  let A : ℝ → ℝ := fun r =>
    (f r + r * deriv f r) * (g r + r * deriv g r)
  let B : ℝ → ℝ := fun r => r ^ 2 * deriv f r * deriv g r
  let J : ℝ → ℝ := fun r => r * f r * g r
  have hDf : Continuous (deriv f) := hf.continuous_deriv_one
  have hDg : Continuous (deriv g) := hg.continuous_deriv_one
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hB : Continuous B := by dsimp [B]; fun_prop
  have hAi := hA.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hBi := hB.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hJ (r : ℝ) : HasDerivAt J (A r - B r) r := by
    have hd := ((hasDerivAt_id r).mul
      ((hf.differentiable (by norm_num) r).hasDerivAt)).mul
      ((hg.differentiable (by norm_num) r).hasDerivAt)
    apply hd.congr_deriv
    dsimp [J, A, B]
    ring
  have hZero : (∫ r in (0 : ℝ)..R, A r - B r) = 0 := by
    have hFt := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hJ r) (hAi.sub hBi)
    simpa [J, mul_assoc, hboundary] using hFt
  rw [intervalIntegral.integral_sub hAi hBi] at hZero
  have hEq : (∫ r in (0 : ℝ)..R, A r) =
      ∫ r in (0 : ℝ)..R, B r := sub_eq_zero.mp hZero
  calc
    (∫ r in (0 : ℝ)..R,
        deriv (radialU f) r * deriv (radialU g) r) =
        ∫ r in (0 : ℝ)..R, A r := by
      apply intervalIntegral.integral_congr
      intro r _
      dsimp [A]
      rw [radialU_deriv f hf r, radialU_deriv g hg r]
    _ = ∫ r in (0 : ℝ)..R, r ^ 2 * deriv f r * deriv g r := hEq

end HBL.Modulation
