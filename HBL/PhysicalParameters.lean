import HBL.DualTestRegularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Conversion of the two implicit coordinates into the manuscript's physical
parameters.  The implicit theorem is most naturally written in
`(log λ, γ)`; the paper states the output as `λ > 0` and phase `γ`.
-/

noncomputable section

open scoped Topology ContDiff

namespace HBL.Modulation

/-- Convert logarithmic scale and phase into positive scale and phase. -/
def physicalParameters (p : Param) : Param :=
  (Real.exp p.1, p.2)

@[simp]
theorem physicalParameters_zero :
    physicalParameters (0 : Param) = (1, 0) := by
  simp [physicalParameters]

theorem physicalParameters_scale_pos (p : Param) :
    0 < (physicalParameters p).1 := by
  simp [physicalParameters, Real.exp_pos]

/-- The log-scale/phase to scale/phase coordinate map is C1 everywhere. -/
theorem physicalParameters_contDiffAt (p : Param) :
    ContDiffAt ℝ 1 physicalParameters p := by
  change ContDiffAt ℝ 1 (fun q : Param => (Real.exp q.1, q.2)) p
  fun_prop

/-- A C1 implicit selector in logarithmic coordinates gives C1 physical
scale and phase, with normalized values `λ=1, γ=0` at the standard bubble. -/
theorem physical_selector_from_log_selector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E → Param) (u₀ : E)
    (hψ0 : ψ u₀ = 0) (hψC1 : ContDiffAt ℝ 1 ψ u₀) :
    let Φ : E → Param := fun u => physicalParameters (ψ u)
    Φ u₀ = (1, 0) ∧
    ContDiffAt ℝ 1 Φ u₀ ∧
    ∀ u, 0 < (Φ u).1 := by
  let Φ : E → Param := fun u => physicalParameters (ψ u)
  refine ⟨?_, ?_, ?_⟩
  · simp [Φ, hψ0]
  · exact (physicalParameters_contDiffAt (ψ u₀)).comp u₀ hψC1
  · intro u
    exact physicalParameters_scale_pos (ψ u)

/-- Positive scale is recovered exactly from its logarithmic coordinate. -/
theorem physicalParameters_log_left_inverse
    {lam gam : ℝ} (hlam : 0 < lam) :
    physicalParameters (Real.log lam, gam) = (lam, gam) := by
  simp [physicalParameters, Real.exp_log hlam]

/-- Logarithmic coordinates are recovered exactly from physical coordinates. -/
theorem log_physicalParameters_left_inverse (p : Param) :
    (Real.log (physicalParameters p).1, (physicalParameters p).2) = p := by
  rcases p with ⟨a, γ⟩
  simp [physicalParameters]

end HBL.Modulation
