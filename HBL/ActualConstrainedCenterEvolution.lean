import HBL.ConstrainedCenterSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Standard constrained centre evolution on the actual HBL centre space

This is the literature-level Kato--Kisyński boundary for the linear
nonautonomous centre equation after the verified moving-frame reduction.
Unlike the earlier provisional boundary, the propagator acts on the actual
closed constrained subspace, so preservation of the scale, phase and single
negative-direction constraints is built into the type.

No blow-up orbit, nonlinear fixed point, shooting graph or main-theorem
conclusion is an input.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.MainBackward

structure ActualConstrainedCenterEvolution where
  U : ℝ → ℝ → ConstrainedCenterSpace →L[ℝ] ConstrainedCenterSpace
  boundConst : ℝ
  boundConst_nonneg : 0 ≤ boundConst
  bound : ∀ s t : ℝ, s ≤ t → ‖U s t‖ ≤ boundConst
  continuous_action :
    Continuous (fun p : (ℝ × ℝ) × ConstrainedCenterSpace =>
      U p.1.1 p.1.2 p.2)
  tail_continuous :
    ∀ (s0 : ℝ) (F : ℝ → ConstrainedCenterSpace),
      Continuous F →
      (∀ s, s0 ≤ s →
        IntegrableOn (fun t => U s t (F t)) (Ioi s)) →
      ContinuousOn
        (fun s => -(∫ t in Ioi s, U s t (F t))) (Ici s0)

/-- A propagated continuous source is strongly measurable on every tail. -/
theorem actualCenter_propagated_measurable
    (CE : ActualConstrainedCenterEvolution)
    (F : ℝ → ConstrainedCenterSpace) (hF : Continuous F)
    (s : ℝ) :
    AEStronglyMeasurable (fun t => CE.U s t (F t))
      (volume.restrict (Ioi s)) := by
  have hp : Continuous (fun t : ℝ => ((s,t), F t)) :=
    (continuous_const.prod_mk continuous_id).prod_mk hF
  exact (CE.continuous_action.comp hp).aestronglyMeasurable.restrict

#print axioms actualCenter_propagated_measurable

end HBL.MainBackward
