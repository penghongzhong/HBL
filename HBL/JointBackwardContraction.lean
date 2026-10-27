import Mathlib.Topology.MetricSpace.Contracting

/-!
# Two-stage backward contraction

This is a generic Banach fixed-point lemma for the repaired HBL backward
scheme.  It is not a new manuscript theorem environment.

The threshold reconstruction maps a centre path to a finite-dimensional
terminal path, and the centre reconstruction maps that terminal path back
to the centre.  Once the two Lipschitz constants have product < 1, the
coupled pair exists and is unique.
-/

noncomputable section
set_option autoImplicit false

open Function

namespace HBL.MainBackward

theorem two_stage_backward_fixed_point
    {X Y : Type*}
    [MetricSpace X] [CompleteSpace X] [Nonempty X]
    [MetricSpace Y]
    (KA KQ : ℝ≥0) (threshold : X → Y) (center : Y → X)
    (hA : LipschitzWith KA threshold)
    (hQ : LipschitzWith KQ center)
    (hsmall : KQ * KA < 1) :
    ∃! z : X × Y,
      z.2 = threshold z.1 ∧ z.1 = center z.2 := by
  let Phi : X → X := fun x => center (threshold x)
  have hLip : LipschitzWith (KQ * KA) Phi := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (Phi x) (Phi y) ≤ (KQ : ℝ) * dist (threshold x) (threshold y) :=
        hQ.dist_le_mul _ _
      _ ≤ (KQ : ℝ) * ((KA : ℝ) * dist x y) := by
        exact mul_le_mul_of_nonneg_left (hA.dist_le_mul x y) (NNReal.zero_le_coe)
      _ = ((KQ * KA : ℝ≥0) : ℝ) * dist x y := by
        push_cast
        ring
  have hPhi : ContractingWith (KQ * KA) Phi := ⟨hsmall, hLip⟩
  let xstar : X := hPhi.fixedPoint Phi
  let ystar : Y := threshold xstar
  have hx : Phi xstar = xstar := hPhi.fixedPoint_isFixedPt
  refine ⟨(xstar, ystar), ?_, ?_⟩
  · exact ⟨rfl, hx.symm⟩
  · intro z hz
    rcases hz with ⟨hzA, hzQ⟩
    have hzfix : Phi z.1 = z.1 := by
      dsimp only [Phi]
      rw [← hzA, hzQ]
    have hzx : z.1 = xstar := by
      change z.1 = hPhi.fixedPoint Phi
      exact hPhi.fixedPoint_unique hzfix
    apply Prod.ext
    · exact hzx
    · rw [hzA, hzx]
      rfl

#print axioms two_stage_backward_fixed_point

end HBL.MainBackward
