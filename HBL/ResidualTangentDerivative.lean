import HBL.RetainedFeedbackTail
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
The derivative is computed from the residual Vtime - N(V), not assumed
as an identity for an arbitrary E. The profile can take values in a
stronger normed domain Z while the nonlinear evolution takes values in X.
This proves a parameter identity at a fixed time. Identification of Ktime
with the time derivative of K requires the physical mixed regularity and
is not silently asserted here. No physical residual decay is postulated.
-/

noncomputable section

namespace HBL.Modulation.TriangularRepair

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The full parameter derivative of a primitive residual, including its
exact sign and the norm equality needed for the retained-feedback bound.
Z may be a common graph-norm domain; N is differentiated from Z into X. -/
theorem residualTangentDerivative_certified
    (V : Y → Z) (Vtime : Y → X) (N : Z → X) (theta : Y)
    (K : Y →L[ℝ] Z) (Ktime : Y →L[ℝ] X) (Nprime : Z →L[ℝ] X)
    (hV : HasFDerivAt V K theta)
    (hVtime : HasFDerivAt Vtime Ktime theta)
    (hN : HasFDerivAt N Nprime (V theta)) :
    let R := fun eta => Vtime eta - N (V eta)
    let E := Nprime.comp K - Ktime
    HasFDerivAt R (Ktime - Nprime.comp K) theta ∧
      E = -fderiv ℝ R theta ∧
      ‖E‖ = ‖fderiv ℝ R theta‖ := by
  dsimp only
  have hR : HasFDerivAt (fun eta => Vtime eta - N (V eta))
      (Ktime - Nprime.comp K) theta :=
    hVtime.sub (hN.comp theta hV)
  have hE : Nprime.comp K - Ktime =
      -fderiv ℝ (fun eta => Vtime eta - N (V eta)) theta := by
    rw [hR.fderiv]
    abel
  refine ⟨hR, hE, ?_⟩
  rw [hE, norm_neg]

end HBL.Modulation.TriangularRepair
