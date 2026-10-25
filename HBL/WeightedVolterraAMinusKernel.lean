import HBL.WeightedVolterraAMinus
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
Close the precise phase-channel zero-space and nonnegative spectral
geometry for the ACTUAL weighted Volterra operator A₋=I-3V*V.

The first transferred unit mode d₀ is a genuine phase zero vector.
Quantitative 4/5 coercivity on d₀-perp, already established from the
exact weighted Green spectrum, forces the entire kernel to be span(d₀)
without assuming completeness of the input singular vectors.
The nonnegative form and its strict positivity transverse to d₀
are consequences, not imported hypotheses.

These are the actual energy-coordinate operator results. Identification
of the kernel generator with the physical bubble W and the full
three-dimensional Hessian remains a separate unfinished step.
-/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem phaseFirstSine_inner_self_one :
    inner ℝ (weightedVolterraSineMode 0) (weightedVolterraSineMode 0) = 1 := by
  rw [real_inner_self_eq_norm_sq,
    weightedVolterraSineMode_orthonormal.norm_eq_one]
  norm_num

private theorem phaseFirstSine_orthogonal_residual
    (x : RealL2 halfLineMeasure) :
    inner ℝ (weightedVolterraSineMode 0)
      (x - inner ℝ (weightedVolterraSineMode 0) x •
        weightedVolterraSineMode 0) = 0 := by
  rw [inner_sub_right, real_inner_smul_right, phaseFirstSine_inner_self_one]
  ring

private theorem phaseFirstSine_ne_zero : weightedVolterraSineMode 0 ≠ 0 := by
  intro hz
  have hnorm := weightedVolterraSineMode_orthonormal.norm_eq_one 0
  rw [hz, norm_zero] at hnorm
  norm_num at hnorm

/-- The actual phase-channel A₋ is nonnegative on the full input L²
energy space, with no extra hypothesis on an arbitrary input. -/
theorem weightedVolterraAMinus_nonneg (x : RealL2 halfLineMeasure) :
    0 ≤ inner ℝ (weightedVolterraAMinus x) x := by
  let g : RealL2 halfLineMeasure :=
    x - inner ℝ (weightedVolterraSineMode 0) x •
      weightedVolterraSineMode 0
  have hgorth : inner ℝ (weightedVolterraSineMode 0) g = 0 :=
    phaseFirstSine_orthogonal_residual x
  have hAg : weightedVolterraAMinus g = weightedVolterraAMinus x := by
    dsimp only [g]
    rw [map_sub, map_smul, weightedVolterraAMinus_zero_sineMode,
      smul_zero, sub_zero]
  have hsym : ∀ u v : RealL2 halfLineMeasure,
      inner ℝ (weightedVolterraAMinus u) v =
        inner ℝ u (weightedVolterraAMinus v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedVolterraAMinus_selfAdjoint
  have hcross :
      inner ℝ (weightedVolterraAMinus x) (weightedVolterraSineMode 0) = 0 := by
    rw [hsym x (weightedVolterraSineMode 0),
      weightedVolterraAMinus_zero_sineMode, inner_zero_right]
  have hquadratic :
      inner ℝ (weightedVolterraAMinus g) g =
        inner ℝ (weightedVolterraAMinus x) x := by
    rw [hAg]
    dsimp only [g]
    rw [inner_sub_right, real_inner_smul_right, hcross, mul_zero, sub_zero]
  have hgap := weightedVolterraAMinus_tail_coercive g hgorth
  rw [hquadratic] at hgap
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 5)
    (sq_nonneg ‖g‖)).trans hgap

/-- The entire genuine phase kernel is exactly the single
actual transferred zero mode, not just a known subset of the kernel. -/
theorem weightedVolterraAMinus_kernel_eq_sine_span :
    weightedVolterraAMinus.ker =
      Submodule.span ℝ {weightedVolterraSineMode 0} := by
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    let g : RealL2 halfLineMeasure :=
      x - inner ℝ (weightedVolterraSineMode 0) x •
        weightedVolterraSineMode 0
    have hgorth : inner ℝ (weightedVolterraSineMode 0) g = 0 :=
      phaseFirstSine_orthogonal_residual x
    have hAg : weightedVolterraAMinus g = 0 := by
      dsimp only [g]
      rw [map_sub, map_smul, weightedVolterraAMinus_zero_sineMode,
        smul_zero, sub_zero, hx]
    have hgap := weightedVolterraAMinus_tail_coercive g hgorth
    rw [hAg, inner_zero_left] at hgap
    have hgzero : g = 0 := by
      have hn : ‖g‖ = 0 := by
        have hnonneg := norm_nonneg g
        nlinarith [sq_nonneg ‖g‖]
      exact norm_eq_zero.mp hn
    apply Submodule.mem_span_singleton.mpr
    refine ⟨inner ℝ (weightedVolterraSineMode 0) x, ?_⟩
    dsimp only [g] at hgzero
    exact (sub_eq_zero.mp hgzero).symm
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    change weightedVolterraAMinus x = 0
    rw [← hc, map_smul, weightedVolterraAMinus_zero_sineMode, smul_zero]

/-- The actual phase-channel kernel has exactly real dimension one. -/
theorem weightedVolterraAMinus_kernel_finrank :
    Module.finrank ℝ weightedVolterraAMinus.ker = 1 := by
  rw [weightedVolterraAMinus_kernel_eq_sine_span]
  exact finrank_span_singleton phaseFirstSine_ne_zero

/-- Strict positivity holds at every nonzero input transverse to the
single phase mode, with a certified spectral gap. -/
theorem weightedVolterraAMinus_strict_positive_off_phase
    (x : RealL2 halfLineMeasure)
    (hx : x ≠ 0)
    (hphase : inner ℝ (weightedVolterraSineMode 0) x = 0) :
    0 < inner ℝ (weightedVolterraAMinus x) x := by
  have hgap := weightedVolterraAMinus_tail_coercive x hphase
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  exact (mul_pos (by norm_num : (0 : ℝ) < 4 / 5)
    (pow_pos hnorm 2)).trans_le hgap

end HBL.Modulation.Monopole
