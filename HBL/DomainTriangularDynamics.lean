import HBL.RetainedFeedbackTail
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Moving triangular coordinates with the unbounded generator defined on
an explicit linear subspace D. Only the coordinate maps are continuous.
No bounded extension of A to X, invariant zero projection, or generator
inverse is assumed. Physical construction of D, K and ell remains separate.
-/

noncomputable section

namespace HBL.Modulation.TriangularRepair

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Exact differentiated moving coordinates on a common linear domain.
The finite-rank coupling is retained. In particular z' need not belong to D;
only z itself is proved to belong to the generator domain at the time s. -/
theorem domainTriangularDynamics_certified
    (D : Submodule ℝ X) (A : D →ₗ[ℝ] X)
    (K : ℝ → Y →L[ℝ] X) (ell : ℝ → X →L[ℝ] Y)
    (v : ℝ → X) (s : ℝ) (Kd : Y →L[ℝ] X) (elld : X →L[ℝ] Y)
    (F : X)
    (hKd : HasDerivAt K Kd s) (helld : HasDerivAt ell elld s)
    (hpair : ∀ t c, ell t (K t c) = c)
    (hKdom : ∀ c, K s c ∈ D) (hvdom : v s ∈ D)
    (hv : HasDerivAt v (A ⟨v s, hvdom⟩ + F) s) :
    let a := fun t => ell t (v t)
    let z := fun t => v t - K t (a t)
    let B := fun w : D => elld w + ell s (A w)
    let E := fun c : Y => A ⟨K s c, hKdom c⟩ - Kd c
    let Q := fun w : X => w - K s (ell s w)
    ∃ hz : z s ∈ D,
      ell s (z s) = 0 ∧
      HasDerivAt a (ell s (E (a s)) + B ⟨z s, hz⟩ + ell s F) s ∧
      HasDerivAt z
        (A ⟨z s, hz⟩ - K s (B ⟨z s, hz⟩) + Q (E (a s)) + Q F) s ∧
      ell s
        (A ⟨z s, hz⟩ - K s (B ⟨z s, hz⟩) + Q (E (a s)) + Q F) =
          -elld (z s) := by
  dsimp only
  let a := fun t => ell t (v t)
  let z := fun t => v t - K t (a t)
  have hz : z s ∈ D := D.sub_mem hvdom (hKdom (a s))
  have horth : ell s (z s) = 0 := by
    dsimp only [z]
    rw [map_sub, hpair]
    exact sub_self _
  have hsplit : v s = K s (a s) + z s := by
    dsimp only [z]
    abel
  have hAsplit : A ⟨v s, hvdom⟩ =
      A ⟨K s (a s), hKdom (a s)⟩ + A ⟨z s, hz⟩ := by
    have heq : (⟨v s, hvdom⟩ : D) =
        (⟨K s (a s), hKdom (a s)⟩ : D) + ⟨z s, hz⟩ := by
      apply Subtype.ext
      exact hsplit
    rw [heq, map_add]
  have hpairD (c : Y) : elld (K s c) + ell s (Kd c) = 0 := by
    have hkc : HasDerivAt (fun t => K t c) (Kd c) s := by
      simpa only [map_zero, add_zero] using
        hKd.clm_apply (hasDerivAt_const s c)
    have h := helld.clm_apply hkc
    have heq : (fun t => ell t (K t c)) = (fun _ : ℝ => c) :=
      funext (fun t => hpair t c)
    rw [heq] at h
    exact h.unique (hasDerivAt_const s c)
  have hsplitd : elld (v s) = elld (K s (a s)) + elld (z s) := by
    exact congrArg elld hsplit |>.trans (map_add elld _ _)
  have hcancel : elld (K s (a s)) = -ell s (Kd (a s)) :=
    eq_neg_of_add_eq_zero_left (hpairD (a s))
  let da := ell s (A ⟨K s (a s), hKdom (a s)⟩ - Kd (a s)) +
    (elld (z s) + ell s (A ⟨z s, hz⟩)) + ell s F
  have hdaeq : elld (v s) + ell s (A ⟨v s, hvdom⟩ + F) = da := by
    dsimp only [da]
    rw [hsplitd, hAsplit]
    simp only [map_add, map_sub, hcancel]
    abel
  have hda : HasDerivAt a da s := by
    have h := helld.clm_apply hv
    rw [hdaeq] at h
    exact h
  let dz := A ⟨z s, hz⟩ - K s (elld (z s) + ell s (A ⟨z s, hz⟩)) +
    ((A ⟨K s (a s), hKdom (a s)⟩ - Kd (a s)) -
      K s (ell s (A ⟨K s (a s), hKdom (a s)⟩ - Kd (a s)))) +
    (F - K s (ell s F))
  have hdzeq : (A ⟨v s, hvdom⟩ + F) -
      (Kd (a s) + K s da) = dz := by
    dsimp only [da, dz]
    rw [hAsplit]
    simp only [map_add, map_sub]
    abel
  have hdz : HasDerivAt z dz s := by
    have h := hv.sub (hKd.clm_apply hda)
    rw [hdzeq] at h
    exact h
  have hconstraint : ell s dz = -elld (z s) := by
    have h := helld.clm_apply hdz
    have heq : (fun t => ell t (z t)) = (fun _ : ℝ => (0 : Y)) := by
      funext t
      dsimp only [z, a]
      rw [map_sub, hpair, sub_self]
    rw [heq] at h
    have hzero := h.unique (hasDerivAt_const s (0 : Y))
    exact eq_neg_of_add_eq_zero_right hzero
  exact ⟨hz, horth, hda, hdz, hconstraint⟩

end HBL.Modulation.TriangularRepair
