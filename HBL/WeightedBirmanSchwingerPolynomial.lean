import HBL.WeightedFreeGreenSpectrum

/-!
The algebraic end of the weighted Birman--Schwinger spectral bridge.

The analytic kernel calculation needed upstream is the single operator
identity `T² (I + G) = 576 G`.  Once this is known, a fixed vector of
`G (9I + T)` satisfies a cubic polynomial in the self-adjoint Hartree
factor.  The other quadratic factor is strictly positive, so the vector
lies in the `T = 6` eigenspace and hence in the `G = 1/15` eigenspace.
-/

noncomputable section

namespace HBL

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The quadratic factor occurring after the Birman--Schwinger cubic is
strictly positive for a self-adjoint real operator. -/
theorem selfAdjoint_quadratic_factor_eq_zero
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) (y : E)
    (hy : T (T y) + (16 : ℝ) • T y + (96 : ℝ) • y = 0) :
    y = 0 := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hinner := congrArg (fun z : E => inner ℝ z y) hy
  have hTT : inner ℝ (T (T y)) y = ‖T y‖ ^ 2 := by
    calc
      inner ℝ (T (T y)) y = inner ℝ (T y) (T y) := hsym (T y) y
      _ = ‖T y‖ ^ 2 := real_inner_self_eq_norm_sq (T y)
  have heq :
      ‖T y‖ ^ 2 + 16 * inner ℝ (T y) y + 96 * ‖y‖ ^ 2 = 0 := by
    rw [inner_add_left, inner_add_left, inner_smul_left,
      inner_smul_left, inner_zero_left, hTT,
      real_inner_self_eq_norm_sq] at hinner
    norm_num at hinner ⊢
    exact hinner
  have hsquare :
      ‖T y + (8 : ℝ) • y‖ ^ 2 =
        ‖T y‖ ^ 2 + 16 * inner ℝ (T y) y + 64 * ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm y (T y)]
    norm_num
    ring
  have hnonneg : 0 ≤ ‖T y + (8 : ℝ) • y‖ ^ 2 := sq_nonneg _
  have hynorm : ‖y‖ ^ 2 = 0 := by
    rw [hsquare] at hnonneg
    nlinarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hynorm)

/-- Abstract polynomial reduction from the kernel identity
`T² (I + G) = 576 G` to the distinguished Green eigenvalue. -/
theorem birmanSchwinger_fixed_implies_green_one_fifteen
    (G T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hkernel : ∀ z : E, T (T (z + G z)) = (576 : ℝ) • G z)
    (x : E) (hfixed : G ((9 : ℝ) • x + T x) = x) :
    G x = (1 / 15 : ℝ) • x := by
  have hcubic := hkernel ((9 : ℝ) • x + T x)
  rw [hfixed] at hcubic
  simp only [map_add, map_smul] at hcubic
  have hcubic' :
      T (T (T x)) + (10 : ℝ) • T (T x) - (576 : ℝ) • x = 0 := by
    calc
      T (T (T x)) + (10 : ℝ) • T (T x) - (576 : ℝ) • x =
          (9 : ℝ) • T (T x) + T (T (T x)) + T (T x) -
            (576 : ℝ) • x := by module
      _ = (576 : ℝ) • x - (576 : ℝ) • x := by
        rw [hcubic]
      _ = 0 := sub_self _
  let y : E := T x - (6 : ℝ) • x
  have hy : T (T y) + (16 : ℝ) • T y + (96 : ℝ) • y = 0 := by
    dsimp [y]
    calc
      T (T (T x - (6 : ℝ) • x)) +
            (16 : ℝ) • T (T x - (6 : ℝ) • x) +
            (96 : ℝ) • (T x - (6 : ℝ) • x) =
          T (T (T x)) + (10 : ℝ) • T (T x) -
            (576 : ℝ) • x := by
              simp only [map_sub, map_smul]
              module
      _ = 0 := hcubic'
  have hyzero := selfAdjoint_quadratic_factor_eq_zero T hT y hy
  have hTx : T x = (6 : ℝ) • x := sub_eq_zero.mp hyzero
  have harg : (9 : ℝ) • x + T x = (15 : ℝ) • x := by
    rw [hTx]
    module
  rw [harg, map_smul] at hfixed
  have hscaled : (15 : ℝ) • G x = x := by
    exact hfixed
  calc
    G x = (1 / 15 : ℝ) • ((15 : ℝ) • G x) := by module
    _ = (1 / 15 : ℝ) • x := by rw [hscaled]

end HBL

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- The analytic identity for the joint weighted Green--Hartree spectral
bridge, proved concretely in `WeightedHartreeSquareIdentity`. -/
def WeightedHartreeSquareGreenIdentity : Prop :=
  ∀ z : RealL2 halfLineMeasure,
    weightedHartreeOperator
        (weightedHartreeOperator (z + weightedFreeGreenOperator z)) =
      (576 : ℝ) • weightedFreeGreenOperator z

/-- The square identity reduces every fixed vector of the concrete
Birman--Schwinger operator to the already classified `1/15` Green
eigenspace. -/
theorem weightedBirmanSchwinger_fixed_mem_span_of_square_identity
    (hidentity : WeightedHartreeSquareGreenIdentity)
    (x : RealL2 halfLineMeasure)
    (hfixed : weightedBirmanSchwingerOperator x = x) :
    x ∈ Submodule.span ℝ {weightedScaleResonanceL2} := by
  have hfixed' :
      weightedFreeGreenOperator
          ((9 : ℝ) • x + weightedHartreeOperator x) = x := by
    simpa only [weightedBirmanSchwingerOperator,
      weightedPotentialOperator, ContinuousLinearMap.comp_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.id_apply] using hfixed
  have heig := HBL.birmanSchwinger_fixed_implies_green_one_fifteen
    weightedFreeGreenOperator weightedHartreeOperator
    weightedHartreeOperator_selfAdjoint hidentity x hfixed'
  exact (weightedFreeGreen_one_fifteen_eigen_iff x).mp heig

/-- Exact concrete fixed-space classification, conditional only on the
explicit square-kernel identity isolated above. -/
theorem weightedBirmanSchwinger_fixed_iff_span_of_square_identity
    (hidentity : WeightedHartreeSquareGreenIdentity)
    (x : RealL2 halfLineMeasure) :
    weightedBirmanSchwingerOperator x = x ↔
      x ∈ Submodule.span ℝ {weightedScaleResonanceL2} := by
  constructor
  · exact weightedBirmanSchwinger_fixed_mem_span_of_square_identity
      hidentity x
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, weightedBirmanSchwinger_scale_fixed]

end HBL.Modulation.Monopole
