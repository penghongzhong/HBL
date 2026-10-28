import HBL.KummerFrozenAnnulus
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic

/-!
# Actual local Kummer ODE solutions

On the physical annulus, z > 0, the frozen Hartree Kummer coefficient is
smooth.  We apply Mathlib Picard-Lindelöf to an autonomous augmented state
(time coordinate, field, first radial derivative), thereby constructing
real, non-placeholder local solutions of the actual frozen Kummer equation.

This is a local IVP theorem; extending it to the entire fixed annulus and
proving the full original one-layer statement remain separate obligations.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Profile.Kummer

/-- Actual frozen Kummer first-order system: z'=1, u'=p,
p'=-a(z)p-b u. -/
abbrev KummerODEState := ℝ × (ℂ × ℂ)

def frozenKummerAugmentedField (mu theta : ℝ) :
    KummerODEState → KummerODEState :=
  fun x => (1,
    (x.2.2, -(frozenFirstCoeff x.1 * x.2.2 +
      frozenZeroCoeff mu theta * x.2.1)))

theorem frozenFirstCoeff_contDiffAt
    (z : ℝ) (hz : z ≠ 0) :
    ContDiffAt ℝ 1 frozenFirstCoeff z := by
  have hcz : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  unfold frozenFirstCoeff
  fun_prop (disch := exact hcz)

theorem frozenZeroCoeff_contDiff
    (mu theta : ℝ) :
    ContDiff ℝ 1 (fun _ : ℝ => frozenZeroCoeff mu theta) := by
  fun_prop

theorem frozenKummerAugmentedField_contDiffAt
    (mu theta z : ℝ) (u p : ℂ) (hz : z ≠ 0) :
    ContDiffAt ℝ 1 (frozenKummerAugmentedField mu theta)
      (z, (u, p)) := by
  have ha := frozenFirstCoeff_contDiffAt z hz
  unfold frozenKummerAugmentedField
  fun_prop (disch := assumption)

theorem exists_local_frozenKummer_augmented_solution
    (mu theta z : ℝ) (u p : ℂ) (hz : 0 < z) :
    ∃ X : ℝ → KummerODEState,
      X 0 = (z, (u, p)) ∧
      ∃ eps : ℝ, 0 < eps ∧
        ∀ t ∈ Set.Ioo (-eps) eps,
          HasDerivAt X (frozenKummerAugmentedField mu theta (X t)) t := by
  have hreg := frozenKummerAugmentedField_contDiffAt
    mu theta z u p hz.ne'
  simpa only [sub_zero, zero_add] using
    (ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      hreg 0)

#print axioms frozenFirstCoeff_contDiffAt
#print axioms frozenKummerAugmentedField_contDiffAt
#print axioms exists_local_frozenKummer_augmented_solution

end HBL.Profile.Kummer
