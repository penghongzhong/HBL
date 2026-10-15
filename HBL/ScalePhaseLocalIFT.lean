import HBL.ScalePhaseJacobian

/-!
Last finite-dimensional assembly of the first manuscript lemma.

The proof no longer assumes the two-by-two Jacobian: that matrix is
deduced from the scale derivative and the phase normalization in
HBL.ScalePhaseJacobian.  The actual radial homogeneous-energy realization
of the two scale-transported test families remains to be supplied.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

section LocalImplicitCoordinates

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The pair of orthogonality constraints, based at a real bubble. -/
def scalePhaseResidual
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ)) (w : V)
    (v : (V × V) × Param) : Param :=
  scalePhaseObservable Splus Sminus v -
    scalePhaseObservable Splus Sminus ((w, (0 : V)), (0 : Param))

@[simp]
theorem scalePhaseResidual_base_zero
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ)) (w : V) :
    scalePhaseResidual Splus Sminus w
      ((w, (0 : V)), (0 : Param)) = 0 := by
  simp [scalePhaseResidual]

/-- C1 regularity of the actual tested constraints, conditional only on
operator-norm C1 regularity of the scale-transported dual test families. -/
theorem scalePhaseResidual_contDiffAt
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ)) (w : V)
    (hPlusC1 : ContDiffAt ℝ 1 Splus (0 : ℝ))
    (hMinusC1 : ContDiffAt ℝ 1 Sminus (0 : ℝ)) :
    ContDiffAt ℝ 1 (scalePhaseResidual Splus Sminus w)
      ((w, (0 : V)), (0 : Param)) := by
  change ContDiffAt ℝ 1
    (fun v : (V × V) × Param =>
      scalePhaseObservable Splus Sminus v -
        scalePhaseObservable Splus Sminus ((w, (0 : V)), (0 : Param)))
    ((w, (0 : V)), (0 : Param))
  exact (scalePhaseObservable_contDiffAt Splus Sminus
    (w, (0 : V)) hPlusC1 hMinusC1).sub_const _

/-- No separate Jacobian hypothesis: the partial Jacobian is -I2
provided the scale-mode normalization and the negative-channel phase
normalization hold. -/
theorem scalePhaseResidual_partial_jacobian
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ)) (w : V)
    (hPlusC1 : ContDiffAt ℝ 1 Splus (0 : ℝ))
    (hMinusC1 : ContDiffAt ℝ 1 Sminus (0 : ℝ))
    (hScale : HasDerivAt (fun a : ℝ => Splus a w) (-1) 0)
    (hMinusNorm : Sminus 0 w = 1) :
    (fderiv ℝ (scalePhaseResidual Splus Sminus w)
      ((w, (0 : V)), (0 : Param))).comp
      (ContinuousLinearMap.inr ℝ (V × V) Param) = parameterNegId := by
  have hF :=
    scalePhaseResidual_contDiffAt Splus Sminus w hPlusC1 hMinusC1
  have hSlice : HasFDerivAt
      (fun p : Param =>
        scalePhaseResidual Splus Sminus w ((w, (0 : V)), p))
      parameterNegId (0 : Param) := by
    change HasFDerivAt
      (fun p : Param =>
        scalePhaseObservable Splus Sminus ((w, (0 : V)), p) -
          scalePhaseObservable Splus Sminus ((w, (0 : V)), (0 : Param)))
      parameterNegId (0 : Param)
    exact (scalePhase_slice_hasFDerivAt Splus Sminus w
      hPlusC1 hMinusC1 hScale hMinusNorm).sub_const _
  exact partial_jacobian_from_slice
    (scalePhaseResidual Splus Sminus w) (w, (0 : V)) hF hSlice

/-- The full local implicit-modulation conclusion at the normalized bubble,
with positive scale, C1 dependence and local uniqueness.  The remaining
analytic interfaces are precisely the two C1 scale-test families and the
scale-column derivative. -/
theorem scalePhase_local_modulation_physical
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ)) (w : V)
    (hPlusC1 : ContDiffAt ℝ 1 Splus (0 : ℝ))
    (hMinusC1 : ContDiffAt ℝ 1 Sminus (0 : ℝ))
    (hScale : HasDerivAt (fun a : ℝ => Splus a w) (-1) 0)
    (hMinusNorm : Sminus 0 w = 1) :
    ∃ Phi : (V × V) → Param,
      Phi (w, (0 : V)) = (1, 0) ∧
      ContDiffAt ℝ 1 Phi (w, (0 : V)) ∧
      (∀ u, 0 < (Phi u).1) ∧
      (∀ᶠ u in 𝓝 (w, (0 : V)),
        scalePhaseResidual Splus Sminus w
          (u, (Real.log (Phi u).1, (Phi u).2)) = 0) ∧
      (∀ᶠ v in 𝓝 ((w, (0 : V)), (0 : Param)),
        (scalePhaseResidual Splus Sminus w v = 0 ↔
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2)) := by
  have hF0 :=
    scalePhaseResidual_base_zero Splus Sminus w
  have hFC1 :=
    scalePhaseResidual_contDiffAt Splus Sminus w hPlusC1 hMinusC1
  have hParam :=
    scalePhaseResidual_partial_jacobian
      Splus Sminus w hPlusC1 hMinusC1 hScale hMinusNorm
  obtain ⟨psi, hpsi0, hpsiC1, hSolve, hUnique⟩ :=
    local_modulation_from_normalized_jacobian
      (F := scalePhaseResidual Splus Sminus w)
      (u₀ := (w, (0 : V))) hF0 hFC1 hParam
  let Phi : (V × V) → Param := fun u => physicalParameters (psi u)
  have hPhi0 : Phi (w, (0 : V)) = (1, 0) := by
    simp [Phi, hpsi0]
  have hPhiC1 : ContDiffAt ℝ 1 Phi (w, (0 : V)) :=
    (physicalParameters_contDiffAt (psi (w, (0 : V)))).comp
      (w, (0 : V)) hpsiC1
  have hPos : ∀ u, 0 < (Phi u).1 := by
    intro u
    exact physicalParameters_scale_pos (psi u)
  have hLog (u : V × V) :
      (Real.log (Phi u).1, (Phi u).2) = psi u :=
    log_physicalParameters_left_inverse (psi u)
  refine ⟨Phi, hPhi0, hPhiC1, hPos, ?_, ?_⟩
  · filter_upwards [hSolve] with u hu
    rw [hLog u]
    exact hu
  · filter_upwards [hUnique] with v hv
    rw [hLog v.1]
    exact hv

end LocalImplicitCoordinates

end HBL.Modulation
