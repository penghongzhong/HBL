import HBL.WeightedFreeGreenSpectrum
import HBL.RadialEnergyIsometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Actual finite-radius energy identity for the arctangent conjugation.
The radial function is q_v(r)=sqrt(1+r^2)*v(arctan r), and the left side
uses its ordinary derivative. The cross term is removed by the actual
boundary primitive r*v(arctan r)^2, without redefining either energy.
This is a classical core statement, not a Hilbert-completion theorem.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace HBL.Modulation.Monopole

/-- Pullback of an angular profile to the actual radial Dirichlet coordinate. -/
def arctanEnergyPullback (v : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.sqrt (1 + r ^ 2) * v (Real.arctan r)

/-- Ordinary derivative of the actual arctangent pullback. -/
theorem arctanEnergyPullback_hasDerivAt
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (r : ℝ) :
    HasDerivAt (arctanEnergyPullback v)
      ((r * v (Real.arctan r) + deriv v (Real.arctan r)) /
        Real.sqrt (1 + r ^ 2)) r := by
  have hs0 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    convert (hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2) using 1
    · funext x
      rfl
    · simp only [id_eq]
      ring
  have hsne : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2))
      (r / Real.sqrt (1 + r ^ 2)) r := by
    convert hs0.sqrt (by positivity) using 1
    field_simp [hsne]
  have hu := ((hv.differentiable (by norm_num) (Real.arctan r)).hasDerivAt).comp
    r (Real.hasDerivAt_arctan' r)
  convert hs.mul hu using 1
  · funext x
    rfl
  · have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
      Real.sq_sqrt (by positivity)
    simp only [Function.comp_def]
    field_simp [hsne]
    rw [hs2]
    ring

/-- Exact radial/angular energy identity, including the actual boundary term. -/
theorem arctanEnergyPullback_energy_identity
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (R : ℝ) :
    (∫ r in (0 : ℝ)..R, (deriv (arctanEnergyPullback v) r) ^ 2) =
      (∫ theta in (0 : ℝ)..Real.arctan R,
        (deriv v theta) ^ 2 - (v theta) ^ 2) +
      R * (v (Real.arctan R)) ^ 2 := by
  let d : ℝ → ℝ := fun r =>
    (r * v (Real.arctan r) + deriv v (Real.arctan r)) /
      Real.sqrt (1 + r ^ 2)
  let g : ℝ → ℝ := fun theta => (deriv v theta) ^ 2 - (v theta) ^ 2
  let A : ℝ → ℝ := fun r => (d r) ^ 2
  let B : ℝ → ℝ := fun r => g (Real.arctan r) * (1 + r ^ 2)⁻¹
  let J : ℝ → ℝ := fun r => r * v (Real.arctan r) ^ 2
  have hvd : Continuous (deriv v) := hv.continuous_deriv_one
  have hvc : Continuous v := hv.continuous
  have hden : ∀ r : ℝ, 1 + r ^ 2 ≠ 0 := fun r => by positivity
  have hsne : ∀ r : ℝ, Real.sqrt (1 + r ^ 2) ≠ 0 := fun r => by positivity
  have hd : Continuous d := by
    dsimp [d]
    exact (continuous_id.mul (hvc.comp Real.continuous_arctan) |>.add
      (hvd.comp Real.continuous_arctan)).div
      (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))) hsne
  have hg : Continuous g := hvd.pow 2 |>.sub (hvc.pow 2)
  have hA : Continuous A := hd.pow 2
  have hB : Continuous B := (hg.comp Real.continuous_arctan).mul
    ((continuous_const.add (continuous_id.pow 2)).inv₀ hden)
  have hAi := hA.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hBi := hB.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hJ (r : ℝ) : HasDerivAt J (A r - B r) r := by
    have hu := ((hv.differentiable (by norm_num) (Real.arctan r)).hasDerivAt).comp
      r (Real.hasDerivAt_arctan' r)
    have h := (hasDerivAt_id r).mul (hu.pow 2)
    apply h.congr_deriv
    dsimp [A, B, d, g]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp [hden r]
    ring
  have hFt := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hJ r) (hAi.sub hBi)
  rw [intervalIntegral.integral_sub hAi hBi] at hFt
  have hChange := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := R)
    (f := Real.arctan) (f' := fun r : ℝ => (1 + r ^ 2)⁻¹)
    (g := g) (fun r _ => Real.hasDerivAt_arctan' r)
    ((continuous_const.add (continuous_id.pow 2)).inv₀ hden).continuousOn hg
  rw [Real.arctan_zero] at hChange
  have hBint : (∫ r in (0 : ℝ)..R, B r) =
      ∫ theta in (0 : ℝ)..Real.arctan R, g theta := hChange
  have hAd : (∫ r in (0 : ℝ)..R, (deriv (arctanEnergyPullback v) r) ^ 2) =
      ∫ r in (0 : ℝ)..R, A r := by
    apply intervalIntegral.integral_congr
    intro r _
    change (deriv (arctanEnergyPullback v) r) ^ 2 = A r
    rw [(arctanEnergyPullback_hasDerivAt v hv r).deriv]
  rw [hAd]
  change (∫ r in (0 : ℝ)..R, A r) =
    (∫ theta in (0 : ℝ)..Real.arctan R, g theta) + R * v (Real.arctan R) ^ 2
  rw [hBint] at hFt
  simp only [J, zero_mul, sub_zero] at hFt
  linarith

/-- If the angular endpoint values vanish, the actual radial coordinate
has zero values at both endpoints and its derivative energy equals the
angular form of -d²-1. -/
theorem arctanEnergyPullback_dirichlet_energy
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (R : ℝ)
    (hzero : v 0 = 0) (hboundary : v (Real.arctan R) = 0) :
    arctanEnergyPullback v 0 = 0 ∧ arctanEnergyPullback v R = 0 ∧
    (∫ r in (0 : ℝ)..R, (deriv (arctanEnergyPullback v) r) ^ 2) =
      ∫ theta in (0 : ℝ)..Real.arctan R,
        (deriv v theta) ^ 2 - (v theta) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [arctanEnergyPullback, hzero]
  · simp [arctanEnergyPullback, hboundary]
  · simpa [hboundary] using arctanEnergyPullback_energy_identity v hv R

end HBL.Modulation.Monopole
