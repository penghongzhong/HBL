import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# C1 differentiation of an unstable shooting tail

Generic parametric Bochner-integral tool for the final HBL shooting graph.
It contains no Hartree spectral or main-theorem conclusion.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.MainBackward

variable {P : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def parameterShootingTail
    (J : P → ℝ → ℝ) (s0 : ℝ) (p : P) : ℝ :=
  -(∫ t in Ioi s0, J p t)

/-- Differentiation of the terminal shooting integral under a uniform
integrable derivative majorant. -/
theorem parameterShootingTail_hasFDerivAt_of_dominated
    (J : P → ℝ → ℝ)
    (J' : P → ℝ → P →L[ℝ] ℝ)
    (p0 : P) (s0 : ℝ) (S : Set P)
    (bound : ℝ → ℝ)
    (hS : S ∈ 𝓝 p0)
    (hJmeas : ∀ᶠ p in 𝓝 p0,
      AEStronglyMeasurable (J p) (volume.restrict (Ioi s0)))
    (hJint : Integrable (J p0) (volume.restrict (Ioi s0)))
    (hJ'meas : AEStronglyMeasurable (J' p0)
      (volume.restrict (Ioi s0)))
    (hbound : ∀ᵐ t ∂volume.restrict (Ioi s0),
      ∀ p ∈ S, ‖J' p t‖ ≤ bound t)
    (hboundInt : Integrable bound (volume.restrict (Ioi s0)))
    (hdiff : ∀ᵐ t ∂volume.restrict (Ioi s0),
      ∀ p ∈ S, HasFDerivAt (fun q => J q t) (J' p t) p) :
    HasFDerivAt (parameterShootingTail J s0)
      (-(∫ t in Ioi s0, J' p0 t)) p0 := by
  have h :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume.restrict (Ioi s0))
      (F := J) (F' := J') (x₀ := p0) (s := S)
      hS hJmeas hJint hJ'meas hbound hboundInt hdiff
  simpa only [parameterShootingTail] using h.neg

/-- In particular, the shooting tail is differentiable whenever the above
dominated derivative hypotheses hold. -/
theorem parameterShootingTail_differentiableAt_of_dominated
    (J : P → ℝ → ℝ)
    (J' : P → ℝ → P →L[ℝ] ℝ)
    (p0 : P) (s0 : ℝ) (S : Set P)
    (bound : ℝ → ℝ)
    (hS : S ∈ 𝓝 p0)
    (hJmeas : ∀ᶠ p in 𝓝 p0,
      AEStronglyMeasurable (J p) (volume.restrict (Ioi s0)))
    (hJint : Integrable (J p0) (volume.restrict (Ioi s0)))
    (hJ'meas : AEStronglyMeasurable (J' p0)
      (volume.restrict (Ioi s0)))
    (hbound : ∀ᵐ t ∂volume.restrict (Ioi s0),
      ∀ p ∈ S, ‖J' p t‖ ≤ bound t)
    (hboundInt : Integrable bound (volume.restrict (Ioi s0)))
    (hdiff : ∀ᵐ t ∂volume.restrict (Ioi s0),
      ∀ p ∈ S, HasFDerivAt (fun q => J q t) (J' p t) p) :
    DifferentiableAt ℝ (parameterShootingTail J s0) p0 :=
  (parameterShootingTail_hasFDerivAt_of_dominated
    J J' p0 s0 S bound hS hJmeas hJint hJ'meas
    hbound hboundInt hdiff).differentiableAt

#print axioms parameterShootingTail_hasFDerivAt_of_dominated
#print axioms parameterShootingTail_differentiableAt_of_dominated

end HBL.MainBackward
