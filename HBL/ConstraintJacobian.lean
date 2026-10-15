import HBL.LocalModulationIFT
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
First manuscript proof target, continued.

This module matches the normalized two test functionals with the two symmetry
tangent directions.  It then transports the Jacobian computation through a
continuously differentiable residual map.  The only remaining manuscript-
specific inputs after this module are the realization of the radial energy
space, boundedness of the two test functionals there, and C1 regularity of
the scale-phase pullback on that space.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

abbrev Param := ℝ × ℝ

section TestPair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pair the two scalar test functionals into one two-component constraint. -/
def testPair (ellPlus ellMinus : E →L[ℝ] ℝ) : E →L[ℝ] Param :=
  ellPlus.prod ellMinus

@[simp]
theorem testPair_apply (ellPlus ellMinus : E →L[ℝ] ℝ) (x : E) :
    testPair ellPlus ellMinus x = (ellPlus x, ellMinus x) := by
  rfl

/-- The two symmetry tangent directions, written in the manuscript order:
scale first and phase second. -/
def symmetryTangent (w z : E) : Param →L[ℝ] E :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (-z)) +
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (-w))

@[simp]
theorem symmetryTangent_apply (w z : E) (p : Param) :
    symmetryTangent w z p = (-p.1) • z + (-p.2) • w := by
  simp [symmetryTangent]

/-- The manuscript normalization and the real/imaginary channel separation
give exactly the matrix `-I₂`. -/
theorem testPair_comp_symmetryTangent
    (ellPlus ellMinus : E →L[ℝ] ℝ) (w z : E)
    (hPlus : ellPlus z = 1) (hMinus : ellMinus w = 1)
    (hPlusCross : ellPlus w = 0) (hMinusCross : ellMinus z = 0) :
    (testPair ellPlus ellMinus).comp (symmetryTangent w z) = parameterNegId := by
  apply ContinuousLinearMap.ext
  intro p
  ext <;>
    simp [testPair, symmetryTangent, parameterNegId,
      hPlus, hMinus, hPlusCross, hMinusCross]

end TestPair

section TestedResidual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Orthogonality constraints obtained by testing a residual. -/
def testedConstraint (ellPlus ellMinus : E →L[ℝ] ℝ)
    (R : E × Param → E) (v : E × Param) : Param :=
  testPair ellPlus ellMinus (R v)

theorem testedConstraint_contDiffAt
    (ellPlus ellMinus : E →L[ℝ] ℝ) (R : E × Param → E)
    (v₀ : E × Param) (hR : ContDiffAt ℝ 1 R v₀) :
    ContDiffAt ℝ 1 (testedConstraint ellPlus ellMinus R) v₀ := by
  simpa [testedConstraint, testPair, Function.comp_def] using
    hR.continuousLinearMap_comp (testPair ellPlus ellMinus)

theorem testedConstraint_hasFDerivAt
    (ellPlus ellMinus : E →L[ℝ] ℝ) (R : E × Param → E)
    (R' : (E × Param) →L[ℝ] E) (v₀ : E × Param)
    (hR : HasFDerivAt R R' v₀) :
    HasFDerivAt (testedConstraint ellPlus ellMinus R)
      ((testPair ellPlus ellMinus).comp R') v₀ := by
  simpa [testedConstraint, testPair, Function.comp_def] using
    (testPair ellPlus ellMinus).hasFDerivAt.comp v₀ hR

/-- The parameter derivative of the tested residual is the normalized
Jacobian once the residual parameter derivative is the two symmetry tangents. -/
theorem testedConstraint_partial_fderiv
    (ellPlus ellMinus : E →L[ℝ] ℝ) (w z : E)
    (R : E × Param → E) (v₀ : E × Param)
    (hR : DifferentiableAt ℝ R v₀)
    (hRparam :
      (fderiv ℝ R v₀).comp (ContinuousLinearMap.inr ℝ E Param) =
        symmetryTangent w z)
    (hPlus : ellPlus z = 1) (hMinus : ellMinus w = 1)
    (hPlusCross : ellPlus w = 0) (hMinusCross : ellMinus z = 0) :
    (fderiv ℝ (testedConstraint ellPlus ellMinus R) v₀).comp
        (ContinuousLinearMap.inr ℝ E Param) = parameterNegId := by
  have hfd :
      fderiv ℝ (testedConstraint ellPlus ellMinus R) v₀ =
        (testPair ellPlus ellMinus).comp (fderiv ℝ R v₀) :=
    (testedConstraint_hasFDerivAt ellPlus ellMinus R
      (fderiv ℝ R v₀) v₀ hR.hasFDerivAt).fderiv
  rw [hfd, ContinuousLinearMap.comp_assoc, hRparam]
  exact testPair_comp_symmetryTangent ellPlus ellMinus w z
    hPlus hMinus hPlusCross hMinusCross

/-- Abstract closure of the manuscript's local modulation proof.
The theorem is intentionally stated at the exact interface still needed from
the radial energy-space implementation. -/
theorem local_modulation_from_tested_residual
    (ellPlus ellMinus : E →L[ℝ] ℝ) (w z : E)
    (R : E × Param → E) (u₀ : E)
    (hR0 : R (u₀, (0 : Param)) = 0)
    (hC1 : ContDiffAt ℝ 1 R (u₀, (0 : Param)))
    (hRparam :
      (fderiv ℝ R (u₀, (0 : Param))).comp
          (ContinuousLinearMap.inr ℝ E Param) =
        symmetryTangent w z)
    (hPlus : ellPlus z = 1) (hMinus : ellMinus w = 1)
    (hPlusCross : ellPlus w = 0) (hMinusCross : ellMinus z = 0) :
    ∃ ψ : E → Param,
      ψ u₀ = 0 ∧
      ContDiffAt ℝ 1 ψ u₀ ∧
      (∀ᶠ u in 𝓝 u₀,
        testedConstraint ellPlus ellMinus R (u, ψ u) = 0) ∧
      (∀ᶠ v in 𝓝 (u₀, (0 : Param)),
        (testedConstraint ellPlus ellMinus R v = 0 ↔ ψ v.1 = v.2)) := by
  have hF0 :
      testedConstraint ellPlus ellMinus R (u₀, (0 : Param)) = 0 := by
    simp [testedConstraint, hR0]
  have hFC1 :
      ContDiffAt ℝ 1 (testedConstraint ellPlus ellMinus R)
        (u₀, (0 : Param)) :=
    testedConstraint_contDiffAt ellPlus ellMinus R _ hC1
  have hDiff : DifferentiableAt ℝ R (u₀, (0 : Param)) :=
    hC1.differentiableAt (by norm_num)
  have hParam :
      (fderiv ℝ (testedConstraint ellPlus ellMinus R)
          (u₀, (0 : Param))).comp
          (ContinuousLinearMap.inr ℝ E Param) = parameterNegId :=
    testedConstraint_partial_fderiv ellPlus ellMinus w z R _ hDiff hRparam
      hPlus hMinus hPlusCross hMinusCross
  exact local_modulation_from_normalized_jacobian
    (F := testedConstraint ellPlus ellMinus R) (u₀ := u₀) hF0 hFC1 hParam

end TestedResidual

end HBL.Modulation
