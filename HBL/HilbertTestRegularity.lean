import HBL.PhysicalParameters
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
Hilbert-space realization of the compactly supported threshold tests used in
the first manuscript lemma.

Once a bounded test functional on the completed energy space is represented
by its Riesz vector, differentiability of a parameter-dependent test is
reduced to differentiability of that vector.  This is the correct Banach
interface for the manuscript's two orthogonality conditions.
-/

noncomputable section

open scoped Topology ContDiff RealInnerProductSpace

namespace HBL.Modulation

section RieszTests

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Riesz vector of a bounded real linear functional. -/
def dualRepresenter (ell : E →L[ℝ] ℝ) : E :=
  (InnerProductSpace.toDual ℝ E).symm ell

@[simp]
theorem dualRepresenter_pairing (ell : E →L[ℝ] ℝ) (u : E) :
    inner ℝ (dualRepresenter ell) u = ell u := by
  exact InnerProductSpace.toDual_symm_apply

/-- The paired orthogonality map written through Riesz vectors. -/
def rieszTestConstraint (zPlus zMinus : Param → E) (c : Param)
    (v : E × Param) : Param :=
  (inner ℝ (zPlus v.2) v.1, inner ℝ (zMinus v.2) v.1) - c

/-- A C1 pair of Riesz vectors gives a jointly C1 orthogonality map in the
state and modulation parameters. -/
theorem rieszTestConstraint_contDiffAt
    (zPlus zMinus : Param → E) (c : Param)
    (u₀ : E) (p₀ : Param)
    (hzPlus : ContDiffAt ℝ 1 zPlus p₀)
    (hzMinus : ContDiffAt ℝ 1 zMinus p₀) :
    ContDiffAt ℝ 1 (rieszTestConstraint zPlus zMinus c) (u₀, p₀) := by
  have hp : ContDiffAt ℝ 1 (fun v : E × Param => v.2) (u₀, p₀) :=
    (ContinuousLinearMap.snd ℝ E Param).contDiff.contDiffAt
  have hu : ContDiffAt ℝ 1 (fun v : E × Param => v.1) (u₀, p₀) :=
    (ContinuousLinearMap.fst ℝ E Param).contDiff.contDiffAt
  have hzP :
      ContDiffAt ℝ 1 (fun v : E × Param => zPlus v.2) (u₀, p₀) :=
    hzPlus.comp (u₀, p₀) hp
  have hzM :
      ContDiffAt ℝ 1 (fun v : E × Param => zMinus v.2) (u₀, p₀) :=
    hzMinus.comp (u₀, p₀) hp
  have hP :
      ContDiffAt ℝ 1 (fun v : E × Param => inner ℝ (zPlus v.2) v.1)
        (u₀, p₀) :=
    hzP.inner ℝ hu
  have hM :
      ContDiffAt ℝ 1 (fun v : E × Param => inner ℝ (zMinus v.2) v.1)
        (u₀, p₀) :=
    hzM.inner ℝ hu
  change ContDiffAt ℝ 1
    (fun v : E × Param =>
      (inner ℝ (zPlus v.2) v.1, inner ℝ (zMinus v.2) v.1) - c)
    (u₀, p₀)
  exact (hP.prodMk hM).sub contDiffAt_const

/-- At a base point, choosing the normalization vector equal to the tested
base state makes the constraint vanish exactly. -/
theorem rieszTestConstraint_base_zero
    (zPlus zMinus : Param → E) (u₀ : E) (p₀ : Param) :
    rieszTestConstraint zPlus zMinus
      (inner ℝ (zPlus p₀) u₀, inner ℝ (zMinus p₀) u₀)
      (u₀, p₀) = 0 := by
  simp [rieszTestConstraint]

end RieszTests

end HBL.Modulation
