import HBL.LocalModulationClosure

/-!
Dual-test closure of the first manuscript lemma.

For the homogeneous energy space it is preferable to move the critical
scale/phase action onto the compact test functions.  Then the nonlinear
constraint has the form
`B(p) u - B(0) u0`, where `B(p)` is a C1 family of bounded dual maps.
This file closes the implicit-function argument directly at that interface.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

section DualClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Local logarithmic modulation from a C1 family of bounded dual tests. -/
theorem local_modulation_from_dual_tests
    (B : Param → (E →L[ℝ] Param)) (u₀ : E)
    (hB : ContDiffAt ℝ 1 B (0 : Param))
    (hparam :
      (fderiv ℝ
          (dualTestConstraint B (B (0 : Param) u₀))
          (u₀, (0 : Param))).comp
        (ContinuousLinearMap.inr ℝ E Param) = parameterNegId) :
    ∃ psi : E → Param,
      psi u₀ = 0 ∧
      ContDiffAt ℝ 1 psi u₀ ∧
      (∀ᶠ u in 𝓝 u₀,
        dualTestConstraint B (B (0 : Param) u₀) (u, psi u) = 0) ∧
      (∀ᶠ v in 𝓝 (u₀, (0 : Param)),
        (dualTestConstraint B (B (0 : Param) u₀) v = 0 ↔
          psi v.1 = v.2)) := by
  have hF0 :
      dualTestConstraint B (B (0 : Param) u₀) (u₀, (0 : Param)) = 0 :=
    dualTestConstraint_base_zero B u₀ (0 : Param)
  have hFC1 :
      ContDiffAt ℝ 1
        (dualTestConstraint B (B (0 : Param) u₀))
        (u₀, (0 : Param)) :=
    dualTestConstraint_contDiffAt B (B (0 : Param) u₀) u₀ (0 : Param) hB
  exact local_modulation_from_normalized_jacobian
    (F := dualTestConstraint B (B (0 : Param) u₀))
    (u₀ := u₀) hF0 hFC1 hparam

/-- Physical scale/phase version of the preceding dual-test theorem.
The output has positive scale and the full local uniqueness clause. -/
theorem local_modulation_physical_from_dual_tests
    (B : Param → (E →L[ℝ] Param)) (u₀ : E)
    (hB : ContDiffAt ℝ 1 B (0 : Param))
    (hparam :
      (fderiv ℝ
          (dualTestConstraint B (B (0 : Param) u₀))
          (u₀, (0 : Param))).comp
        (ContinuousLinearMap.inr ℝ E Param) = parameterNegId) :
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
  obtain ⟨psi, hpsi0, hpsiC1, hsolve, huniq⟩ :=
    local_modulation_from_dual_tests B u₀ hB hparam
  let Phi : E → Param := fun u => physicalParameters (psi u)
  have hPhi0 : Phi u₀ = (1, 0) := by
    simp [Phi, hpsi0]
  have hPhiC1 : ContDiffAt ℝ 1 Phi u₀ := by
    exact (physicalParameters_contDiffAt (psi u₀)).comp u₀ hpsiC1
  have hPhiPos : ∀ u, 0 < (Phi u).1 := by
    intro u
    exact physicalParameters_scale_pos (psi u)
  have hlog (u : E) :
      (Real.log (Phi u).1, (Phi u).2) = psi u := by
    exact log_physicalParameters_left_inverse (psi u)
  refine ⟨Phi, hPhi0, hPhiC1, hPhiPos, ?_, ?_⟩
  · filter_upwards [hsolve] with u hu
    rw [hlog u]
    exact hu
  · filter_upwards [huniq] with v hv
    rw [hlog v.1]
    exact hv

end DualClosure

end HBL.Modulation
