import Mathlib.Tactic

/-!
# Explicit free remote blocks

This file formalizes the two algebraic parts of the manuscript's remote
inverse.  The generic phase block is inverted pointwise, and the finite
upper-triangular logarithmic block is solved recursively with uniqueness.
The exceptional k=-1 first-order integral block is intentionally separate.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Profile.Remote

/-- A scalar principal block.  In the manuscript
`c = -k(k+1)/4` and the radial factor is `r^2`. -/
def principalBlock (c r g : ℂ) : ℂ :=
  c * r ^ 2 * g

def principalInverse (c r F : ℂ) : ℂ :=
  F / (c * r ^ 2)

theorem principalInverse_right
    (c r F : ℂ) (hc : c ≠ 0) (hr : r ≠ 0) :
    principalBlock c r (principalInverse c r F) = F := by
  unfold principalBlock principalInverse
  field_simp [hc, hr]

theorem principalInverse_left
    (c r g : ℂ) (hc : c ≠ 0) (hr : r ≠ 0) :
    principalInverse c r (principalBlock c r g) = g := by
  unfold principalBlock principalInverse
  field_simp [hc, hr]

/-- The generic remote coefficient `-k(k+1)/4`. -/
def genericCoefficient (k : ℂ) : ℂ :=
  -(k * (k + 1) / 4)

theorem genericCoefficient_ne_zero
    (k : ℂ) (hk0 : k ≠ 0) (hkm1 : k ≠ -1) :
    genericCoefficient k ≠ 0 := by
  have hk1 : k + 1 ≠ 0 := by
    intro hz
    apply hkm1
    calc
      k = (k + 1) - 1 := by ring
      _ = -1 := by rw [hz]; ring
  unfold genericCoefficient
  exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hk0 hk1) (by norm_num))

theorem genericRemoteInverse_right
    (k r F : ℂ) (hk0 : k ≠ 0) (hkm1 : k ≠ -1) (hr : r ≠ 0) :
    principalBlock (genericCoefficient k) r
      (principalInverse (genericCoefficient k) r F) = F :=
  principalInverse_right _ _ _ (genericCoefficient_ne_zero k hk0 hkm1) hr

/-- Finite upper-triangular logarithmic equations, ordered from the current
log power to the highest one.  Missing next coefficient at the top is zero. -/
def logEquation (varpi : ℂ) (ell : ℕ) :
    List ℂ → List ℂ → Prop
  | [], [] => True
  | F :: Fs, g :: gs =>
      varpi * g - ((ell + 1 : ℕ) : ℂ) * gs.headD 0 = F ∧
        logEquation varpi (ell + 1) Fs gs
  | _, _ => False

/-- Backward recursion
`g_ell = varpi^{-1}(F_ell + (ell+1)g_{ell+1})`. -/
def logSolve (varpi : ℂ) (ell : ℕ) : List ℂ → List ℂ
  | [] => []
  | F :: Fs =>
      let gs := logSolve varpi (ell + 1) Fs
      ((F + ((ell + 1 : ℕ) : ℂ) * gs.headD 0) / varpi) :: gs

theorem logSolve_equation
    (varpi : ℂ) (hvarpi : varpi ≠ 0) :
    ∀ (ell : ℕ) (Fs : List ℂ),
      logEquation varpi ell Fs (logSolve varpi ell Fs) := by
  intro ell Fs
  induction Fs generalizing ell with
  | nil =>
      simp [logSolve, logEquation]
  | cons F Fs ih =>
      rw [logSolve]
      simp only [logEquation]
      constructor
      · field_simp [hvarpi]
        ring
      · exact ih (ell + 1)

theorem logSolve_unique
    (varpi : ℂ) (hvarpi : varpi ≠ 0) :
    ∀ (ell : ℕ) (Fs gs : List ℂ),
      logEquation varpi ell Fs gs →
        gs = logSolve varpi ell Fs := by
  intro ell Fs
  induction Fs generalizing ell with
  | nil =>
      intro gs h
      cases gs with
      | nil => rfl
      | cons g gs =>
          simp [logEquation] at h
  | cons F Fs ih =>
      intro gs h
      cases gs with
      | nil =>
          simp [logEquation] at h
      | cons g gs =>
          have h0 :
              varpi * g - ((ell + 1 : ℕ) : ℂ) * gs.headD 0 = F := h.1
          have ht : logEquation varpi (ell + 1) Fs gs := h.2
          have hgs : gs = logSolve varpi (ell + 1) Fs :=
            ih (ell + 1) gs ht
          subst gs
          rw [logSolve]
          congr 1
          apply (eq_div_iff hvarpi).2
          linear_combination h0

theorem existsUnique_logSolve
    (varpi : ℂ) (hvarpi : varpi ≠ 0)
    (ell : ℕ) (Fs : List ℂ) :
    ∃! gs : List ℂ, logEquation varpi ell Fs gs := by
  refine ⟨logSolve varpi ell Fs, logSolve_equation varpi hvarpi ell Fs, ?_⟩
  intro gs hgs
  exact logSolve_unique varpi hvarpi ell Fs gs hgs

#print axioms principalInverse_right
#print axioms genericCoefficient_ne_zero
#print axioms genericRemoteInverse_right
#print axioms logSolve_equation
#print axioms logSolve_unique
#print axioms existsUnique_logSolve

end HBL.Profile.Remote
