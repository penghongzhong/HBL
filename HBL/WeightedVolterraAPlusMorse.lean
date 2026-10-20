import HBL.WeightedVolterraAPlusModes
import HBL.WeightedVolterraAPlusCoercivity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
HBL: negative index one for the actual bounded
Volterra-channel operator on the concrete half-line L² space.

The two-mode coercivity theorem, the actual zero mode, and self-adjointness
imply nonnegativity on the complement of the first transferred sine mode.
Every strictly negative subspace therefore injects into the real line by
its first sine coefficient. Finite dimensionality is proved rather than
assumed, so the finrank bound is not vacuous on infinite-dimensional spaces.
The first sine span attains dimension one and is strictly negative.

This does not identify the physical Hessian or close the blowup theorem.
-/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- Removing only the first transferred sine mode makes the actual form
nonnegative. The second mode may remain because it is an actual zero mode. -/
theorem weightedVolterraAPlus_nonneg_of_orthogonal_negative
    (f : RealL2 halfLineMeasure)
    (hfirst : inner ℝ (weightedVolterraSineMode 0) f = 0) :
    0 ≤ inner ℝ (weightedVolterraAPlus f) f := by
  let g : RealL2 halfLineMeasure :=
    f - inner ℝ (weightedVolterraSineMode 1) f • weightedVolterraSineMode 1
  have h01 : inner ℝ (weightedVolterraSineMode 0) (weightedVolterraSineMode 1) = 0 :=
    weightedVolterraSineMode_orthonormal.inner_eq_zero (by decide)
  have h11 : inner ℝ (weightedVolterraSineMode 1) (weightedVolterraSineMode 1) = 1 := by
    rw [real_inner_self_eq_norm_sq, weightedVolterraSineMode_orthonormal.norm_eq_one]
    norm_num
  have hgfirst : inner ℝ (weightedVolterraSineMode 0) g = 0 := by
    dsimp only [g]
    rw [inner_sub_right, real_inner_smul_right, hfirst, h01]
    ring
  have hgsecond : inner ℝ (weightedVolterraSineMode 1) g = 0 := by
    dsimp only [g]
    rw [inner_sub_right, real_inner_smul_right, h11]
    ring
  have hAg : weightedVolterraAPlus g = weightedVolterraAPlus f := by
    dsimp only [g]
    rw [map_sub, map_smul, weightedVolterraAPlus_zero_sineMode, smul_zero, sub_zero]
  have hsym : ∀ x y : RealL2 halfLineMeasure,
      inner ℝ (weightedVolterraAPlus x) y =
        inner ℝ x (weightedVolterraAPlus y) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedVolterraAPlus_selfAdjoint
  have hcross : inner ℝ (weightedVolterraAPlus f) (weightedVolterraSineMode 1) = 0 := by
    rw [hsym f (weightedVolterraSineMode 1), weightedVolterraAPlus_zero_sineMode,
      inner_zero_right]
  have hquadratic : inner ℝ (weightedVolterraAPlus g) g =
      inner ℝ (weightedVolterraAPlus f) f := by
    rw [hAg]
    dsimp only [g]
    rw [inner_sub_right, real_inner_smul_right, hcross, mul_zero, sub_zero]
  have hcoercive := weightedVolterraAPlus_tail_coercive g hgfirst hgsecond
  rw [hquadratic] at hcoercive
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 22 / 35) (sq_nonneg ‖g‖)).trans
    hcoercive

/-- Every strictly negative subspace is finite dimensional and has dimension
at most one. No finite-dimensional hypothesis on the subspace is imposed. -/
theorem weightedVolterraAPlus_negative_subspace_finite
    (S : Submodule ℝ (RealL2 halfLineMeasure))
    (hnegative : ∀ f : S, f ≠ 0 →
      inner ℝ (weightedVolterraAPlus (f : RealL2 halfLineMeasure))
        (f : RealL2 halfLineMeasure) < 0) :
    FiniteDimensional ℝ S ∧ Module.finrank ℝ S ≤ 1 := by
  let L : S →ₗ[ℝ] ℝ :=
    (innerₛₗ ℝ (weightedVolterraSineMode 0)).comp S.subtype
  have hL : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    by_contra hfzero
    have horth : inner ℝ (weightedVolterraSineMode 0)
        (f : RealL2 halfLineMeasure) = 0 := by
      change L f = 0
      exact hf
    have hnonnegative :=
      weightedVolterraAPlus_nonneg_of_orthogonal_negative
        (f : RealL2 halfLineMeasure) horth
    have hstrict := hnegative f hfzero
    linarith
  refine ⟨FiniteDimensional.of_injective L hL, ?_⟩
  have hdimension := LinearMap.finrank_le_finrank_of_injective (f := L) hL
  simpa only [Module.finrank_self] using hdimension

/-- Every nonzero vector in the first transferred sine span is strictly
negative for the actual Volterra-channel quadratic form. -/
theorem weightedVolterraAPlus_negative_on_first_span
    (f : RealL2 halfLineMeasure)
    (hmem : f ∈ Submodule.span ℝ {weightedVolterraSineMode 0})
    (hf : f ≠ 0) :
    inner ℝ (weightedVolterraAPlus f) f < 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc0 : c ≠ 0 := by
    intro hz
    apply hf
    rw [hz, zero_smul] at hc
    exact hc.symm
  rw [← hc, map_smul, real_inner_smul_left, real_inner_smul_right,
    weightedVolterraAPlus_negative_quadratic]
  nlinarith [sq_pos_of_ne_zero hc0]

/-- The first transferred sine span is a one-dimensional strictly negative
subspace. Together with the preceding upper bound, it attains index one. -/
theorem weightedVolterraAPlus_negative_subspace_exists :
    ∃ S : Submodule ℝ (RealL2 halfLineMeasure),
      FiniteDimensional ℝ S ∧ Module.finrank ℝ S = 1 ∧
        ∀ f : S, f ≠ 0 →
          inner ℝ (weightedVolterraAPlus (f : RealL2 halfLineMeasure))
            (f : RealL2 halfLineMeasure) < 0 := by
  let S : Submodule ℝ (RealL2 halfLineMeasure) :=
    Submodule.span ℝ {weightedVolterraSineMode 0}
  have hnegative : ∀ f : S, f ≠ 0 →
      inner ℝ (weightedVolterraAPlus (f : RealL2 halfLineMeasure))
        (f : RealL2 halfLineMeasure) < 0 := by
    intro f hf
    apply weightedVolterraAPlus_negative_on_first_span (f : RealL2 halfLineMeasure)
      f.property
    intro hzero
    apply hf
    exact Subtype.ext hzero
  have hnonzero : weightedVolterraSineMode 0 ≠ 0 := by
    intro hzero
    have hnorm := weightedVolterraSineMode_orthonormal.norm_eq_one 0
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  refine ⟨S, (weightedVolterraAPlus_negative_subspace_finite S hnegative).1,
    ?_, hnegative⟩
  exact finrank_span_singleton hnonzero

/-- An explicit index-one characterization: a strictly negative subspace
of dimension one exists, and every strictly negative subspace has dimension
at most one and is finite dimensional. This describes only the actual
bounded Volterra-channel operator, not the physical radial Hessian. -/
theorem weightedVolterraAPlus_morse_index_one :
    (∃ S : Submodule ℝ (RealL2 halfLineMeasure),
      FiniteDimensional ℝ S ∧ Module.finrank ℝ S = 1 ∧
        ∀ f : S, f ≠ 0 →
          inner ℝ (weightedVolterraAPlus (f : RealL2 halfLineMeasure))
            (f : RealL2 halfLineMeasure) < 0) ∧
    (∀ S : Submodule ℝ (RealL2 halfLineMeasure),
      (∀ f : S, f ≠ 0 →
        inner ℝ (weightedVolterraAPlus (f : RealL2 halfLineMeasure))
          (f : RealL2 halfLineMeasure) < 0) →
      FiniteDimensional ℝ S ∧ Module.finrank ℝ S ≤ 1) :=
  ⟨weightedVolterraAPlus_negative_subspace_exists,
    weightedVolterraAPlus_negative_subspace_finite⟩

end HBL.Modulation.Monopole
