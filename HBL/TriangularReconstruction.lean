import HBL.DomainTriangularDynamics
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Reverse reconstruction of the retained triangular coordinates

This is an unnumbered algebraic bridge for the final HBL main theorem.
It proves the converse of the already verified moving-coordinate identity:
if the retained threshold coordinate and constrained centre component solve
their triangular equations, then v = K a + z solves the original strong
linearized equation on the common generator domain.

No propagator, blow-up orbit, spectral projection, or nonlinear conclusion
is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Modulation.TriangularRepair

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Reverse algebraic reconstruction of the original strong equation from
the retained triangular coordinate equations. -/
theorem domainTriangularDynamics_reconstruct
    (D : Submodule ℝ X) (A : D →ₗ[ℝ] X)
    (K : ℝ → Y →L[ℝ] X) (ell : ℝ → X →L[ℝ] Y)
    (a : ℝ → Y) (z : ℝ → X)
    (s : ℝ) (Kd : Y →L[ℝ] X) (elld : X →L[ℝ] Y)
    (F : X)
    (hKd : HasDerivAt K Kd s)
    (hKdom : ∀ c, K s c ∈ D)
    (hzdom : z s ∈ D)
    (ha : HasDerivAt a
      (ell s (A ⟨K s (a s), hKdom (a s)⟩ - Kd (a s)) +
        (elld (z s) + ell s (A ⟨z s, hzdom⟩)) +
        ell s F) s)
    (hz : HasDerivAt z
      (A ⟨z s, hzdom⟩ -
        K s (elld (z s) + ell s (A ⟨z s, hzdom⟩)) +
        ((A ⟨K s (a s), hKdom (a s)⟩ - Kd (a s)) -
          K s (ell s
            (A ⟨K s (a s), hKdom (a s)⟩ - Kd (a s)))) +
        (F - K s (ell s F))) s) :
    ∃ hvdom : K s (a s) + z s ∈ D,
      HasDerivAt (fun t => K t (a t) + z t)
        (A ⟨K s (a s) + z s, hvdom⟩ + F) s := by
  have hvdom : K s (a s) + z s ∈ D :=
    D.add_mem (hKdom (a s)) hzdom
  have hAsplit :
      A ⟨K s (a s) + z s, hvdom⟩ =
        A ⟨K s (a s), hKdom (a s)⟩ + A ⟨z s, hzdom⟩ := by
    have heq :
        (⟨K s (a s) + z s, hvdom⟩ : D) =
          (⟨K s (a s), hKdom (a s)⟩ : D) + ⟨z s, hzdom⟩ := by
      apply Subtype.ext
      rfl
    rw [heq, map_add]
  have hKa :
      HasDerivAt (fun t => K t (a t))
        (Kd (a s) +
          K s
            (ell s (A ⟨K s (a s), hKdom (a s)⟩ - Kd (a s)) +
              (elld (z s) + ell s (A ⟨z s, hzdom⟩)) +
              ell s F)) s := by
    exact hKd.clm_apply ha
  have hv := hKa.add hz
  have hcollapse :
      (Kd (a s) +
          K s
            (ell s (A ⟨K s (a s), hKdom (a s)⟩ - Kd (a s)) +
              (elld (z s) + ell s (A ⟨z s, hzdom⟩)) +
              ell s F)) +
        (A ⟨z s, hzdom⟩ -
          K s (elld (z s) + ell s (A ⟨z s, hzdom⟩)) +
          ((A ⟨K s (a s), hKdom (a s)⟩ - Kd (a s)) -
            K s (ell s
              (A ⟨K s (a s), hKdom (a s)⟩ - Kd (a s)))) +
          (F - K s (ell s F))) =
        A ⟨K s (a s) + z s, hvdom⟩ + F := by
    rw [hAsplit]
    simp only [map_add, map_sub]
    abel
  rw [hcollapse] at hv
  exact ⟨hvdom, hv⟩

#print axioms domainTriangularDynamics_reconstruct

end HBL.Modulation.TriangularRepair
