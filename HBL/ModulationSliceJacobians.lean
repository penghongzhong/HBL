import HBL.DualTestClosure

/-!
Jacobian extraction for the first manuscript lemma.

The parameter Jacobian of a joint state-parameter constraint equals the
Fréchet derivative of its two-dimensional parameter slice at the base state.
This eliminates the previously supplied joint-Jacobian assumption.  The
remaining analytic input is now a parameter-slice derivative, exactly the
two differentiated orthogonality conditions stated in the manuscript.
-/

noncomputable section

open Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace HBL.Modulation

section SliceDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A parameter-slice derivative is the partial Fréchet derivative of the
joint constraint.  This is a chain-rule identity, not an additional
nondegeneracy assumption. -/
theorem partial_jacobian_from_slice
    (F : E × Param → Param) (u₀ : E)
    (hF : ContDiffAt ℝ 1 F (u₀, (0 : Param)))
    (hSlice : HasFDerivAt (fun p : Param => F (u₀, p))
      parameterNegId (0 : Param)) :
    (fderiv ℝ F (u₀, (0 : Param))).comp
      (ContinuousLinearMap.inr ℝ E Param) = parameterNegId := by
  have hDiff : HasFDerivAt F (fderiv ℝ F (u₀, (0 : Param)))
      (u₀, (0 : Param)) :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hInr : HasFDerivAt (fun p : Param => (u₀, p))
      (ContinuousLinearMap.inr ℝ E Param) (0 : Param) :=
    hasFDerivAt_prodMk_right u₀ (0 : Param)
  have hComp : HasFDerivAt (fun p : Param => F (u₀, p))
      ((fderiv ℝ F (u₀, (0 : Param))).comp
        (ContinuousLinearMap.inr ℝ E Param)) (0 : Param) :=
    hDiff.comp (0 : Param) hInr
  exact hComp.unique hSlice

/-- Pointwise parameter differentiation of the dual tests supplies the joint
Jacobian required by the implicit-function theorem. -/
theorem dualTest_partial_jacobian_from_slice
    (B : Param → (E →L[ℝ] Param)) (u₀ : E)
    (hB : ContDiffAt ℝ 1 B (0 : Param))
    (hSlice : HasFDerivAt (fun p : Param => B p u₀)
      parameterNegId (0 : Param)) :
    (fderiv ℝ (dualTestConstraint B (B (0 : Param) u₀))
      (u₀, (0 : Param))).comp
      (ContinuousLinearMap.inr ℝ E Param) = parameterNegId := by
  have hF := dualTestConstraint_contDiffAt B (B (0 : Param) u₀) u₀
    (0 : Param) hB
  have hSlice' : HasFDerivAt
      (fun p : Param => dualTestConstraint B (B (0 : Param) u₀) (u₀, p))
      parameterNegId (0 : Param) := by
    change HasFDerivAt (fun p : Param => B p u₀ - B (0 : Param) u₀)
      parameterNegId (0 : Param)
    exact hSlice.sub_const (B (0 : Param) u₀)
  exact partial_jacobian_from_slice _ u₀ hF hSlice'

/-- Physical local modulation derived from the actual parameter-slice
calculation, not from a separately postulated joint Jacobian. -/
theorem local_modulation_physical_from_dual_slice
    (B : Param → (E →L[ℝ] Param)) (u₀ : E)
    (hB : ContDiffAt ℝ 1 B (0 : Param))
    (hSlice : HasFDerivAt (fun p : Param => B p u₀)
      parameterNegId (0 : Param)) :
    ∃ Phi : E → Param,
      Phi u₀ = (1, 0) ∧
      ContDiffAt ℝ 1 Phi u₀ ∧
      (∀ u, 0 < (Phi u).1) ∧
      (∀ᶠ u in 𝓝 u₀,
        dualTestConstraint B (B (0 : Param) u₀)
          (u, (Real.log (Phi u).1, (Phi u).2)) = 0) ∧
      (∀ᶠ v in 𝓝 (u₀, (0 : Param)),
        (dualTestConstraint B (B (0 : Param) u₀) v = 0 ↔
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2)) := by
  exact local_modulation_physical_from_dual_tests B u₀ hB
    (dualTest_partial_jacobian_from_slice B u₀ hB hSlice)

end SliceDerivative

section RieszSliceDerivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Riesz-vector realization of the implicit step. The two test-vector
families are C1, and the parameter-slice derivative is checked on the bubble
via the two channel normalizations. -/
theorem local_modulation_physical_from_riesz_slice
    (zPlus zMinus : Param → E) (u₀ : E)
    (hzPlus : ContDiffAt ℝ 1 zPlus (0 : Param))
    (hzMinus : ContDiffAt ℝ 1 zMinus (0 : Param))
    (hSlice : HasFDerivAt
      (fun p : Param => (inner ℝ (zPlus p) u₀, inner ℝ (zMinus p) u₀))
      parameterNegId (0 : Param)) :
    ∃ Phi : E → Param,
      Phi u₀ = (1, 0) ∧
      ContDiffAt ℝ 1 Phi u₀ ∧
      (∀ u, 0 < (Phi u).1) ∧
      (∀ᶠ u in 𝓝 u₀,
        rieszTestConstraint zPlus zMinus
          (inner ℝ (zPlus 0) u₀, inner ℝ (zMinus 0) u₀)
          (u, (Real.log (Phi u).1, (Phi u).2)) = 0) ∧
      (∀ᶠ v in 𝓝 (u₀, (0 : Param)),
        (rieszTestConstraint zPlus zMinus
          (inner ℝ (zPlus 0) u₀, inner ℝ (zMinus 0) u₀) v = 0 ↔
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2)) := by
  let c : Param := (inner ℝ (zPlus 0) u₀, inner ℝ (zMinus 0) u₀)
  let F : E × Param → Param := rieszTestConstraint zPlus zMinus c
  have hF0 : F (u₀, (0 : Param)) = 0 := by
    exact rieszTestConstraint_base_zero zPlus zMinus u₀ (0 : Param)
  have hFC1 : ContDiffAt ℝ 1 F (u₀, (0 : Param)) :=
    rieszTestConstraint_contDiffAt zPlus zMinus c u₀ (0 : Param)
      hzPlus hzMinus
  have hSlice' : HasFDerivAt (fun p : Param => F (u₀, p))
      parameterNegId (0 : Param) := by
    change HasFDerivAt
      (fun p : Param =>
        (inner ℝ (zPlus p) u₀, inner ℝ (zMinus p) u₀) - c)
      parameterNegId (0 : Param)
    exact hSlice.sub_const c
  have hParam :
      (fderiv ℝ F (u₀, (0 : Param))).comp
        (ContinuousLinearMap.inr ℝ E Param) = parameterNegId :=
    partial_jacobian_from_slice F u₀ hFC1 hSlice'
  obtain ⟨psi, hpsi0, hpsiC1, hSolve, hUnique⟩ :=
    local_modulation_from_normalized_jacobian F u₀ hF0 hFC1 hParam
  let Phi : E → Param := fun u => physicalParameters (psi u)
  have hPhi0 : Phi u₀ = (1, 0) := by
    simp [Phi, hpsi0]
  have hPhiC1 : ContDiffAt ℝ 1 Phi u₀ :=
    (physicalParameters_contDiffAt (psi u₀)).comp u₀ hpsiC1
  have hPos : ∀ u, 0 < (Phi u).1 := by
    intro u
    exact physicalParameters_scale_pos (psi u)
  have hLog (u : E) :
      (Real.log (Phi u).1, (Phi u).2) = psi u :=
    log_physicalParameters_left_inverse (psi u)
  refine ⟨Phi, hPhi0, hPhiC1, hPos, ?_, ?_⟩
  · filter_upwards [hSolve] with u hu
    rw [hLog u]
    exact hu
  · filter_upwards [hUnique] with v hv
    rw [hLog v.1]
    exact hv

end RieszSliceDerivative

end HBL.Modulation
