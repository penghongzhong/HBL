import HBL.KummerLocalODE
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Recover the physical Kummer radial coordinate from actual IVP curves

The local IVP in KummerLocalODE was formulated as an autonomous augmented
system. Here its first component is proved to equal the genuine radial
coordinate z+t on the whole local existence interval.  The remaining
components then obey the *actual* frozen second-order Hartree Kummer
equation, rather than an abstract ODE with an unspecified coefficient.

The extension from a local interval to the manuscript's full compact
annulus is a separate analytic obligation.
-/

noncomputable section
set_option autoImplicit false

open Set

namespace HBL.Profile.Kummer

theorem frozenKummer_augmented_derivatives
    (mu theta : ℝ) (X : ℝ → KummerODEState)
    {t : ℝ}
    (hODE : HasDerivAt X (frozenKummerAugmentedField mu theta (X t)) t) :
    HasDerivAt (fun s : ℝ => (X s).1) 1 t ∧
    HasDerivAt (fun s : ℝ => (X s).2.1) (X t).2.2 t ∧
    HasDerivAt (fun s : ℝ => (X s).2.2)
      (-(frozenFirstCoeff (X t).1 * (X t).2.2 +
        frozenZeroCoeff mu theta * (X t).2.1)) t := by
  have hz := hODE.fst
  have hu := hODE.snd.fst
  have hp := hODE.snd.snd
  refine ⟨?_, ?_, ?_⟩
  · simpa [frozenKummerAugmentedField] using hz.hasDerivAtFilter
  · simpa [frozenKummerAugmentedField] using hu.hasDerivAtFilter
  · simpa [frozenKummerAugmentedField] using hp.hasDerivAtFilter

/-- First coordinate of every actual augmented solution: z(t) = z0+t.
This is proved from the differential equation, not assumed as a
parametrization condition. -/
theorem frozenKummer_trajectory_time_coordinate
    (mu theta z0 : ℝ) (u0 p0 : ℂ) (eps : ℝ)
    (heps : 0 < eps)
    (X : ℝ → KummerODEState)
    (hX0 : X 0 = (z0, (u0, p0)))
    (hODE : ∀ t ∈ Ioo (-eps) eps,
      HasDerivAt X (frozenKummerAugmentedField mu theta (X t)) t) :
    ∀ t ∈ Ioo (-eps) eps, (X t).1 = z0 + t := by
  let f : ℝ → ℝ := fun t => (X t).1
  let g : ℝ → ℝ := fun t => z0 + t
  have hfd (t : ℝ) (ht : t ∈ Ioo (-eps) eps) :
      HasDerivAt f 1 t := by
    have h := (frozenKummer_augmented_derivatives mu theta X (hODE t ht)).1
    exact h
  have hgd (t : ℝ) : HasDerivAt g 1 t := by
    simpa only [g, Pi.add_apply, id_eq, zero_add] using!
      (hasDerivAt_const t z0).add (hasDerivAt_id t)
  have hdiff_f : DifferentiableOn ℝ f (Ioo (-eps) eps) :=
    fun t ht => (hfd t ht).differentiableAt.differentiableWithinAt
  have hdiff_g : DifferentiableOn ℝ g (Ioo (-eps) eps) :=
    fun t _ht => (hgd t).differentiableAt.differentiableWithinAt
  have hder : Set.EqOn (deriv f) (deriv g) (Ioo (-eps) eps) := by
    intro t ht
    rw [(hfd t ht).deriv, (hgd t).deriv]
  have hzero : (0 : ℝ) ∈ Ioo (-eps) eps := by
    constructor <;> linarith
  have hinit : f 0 = g 0 := by
    dsimp [f, g]
    rw [hX0]
    ring
  have hEq :=
    IsOpen.eqOn_of_deriv_eq isOpen_Ioo isPreconnected_Ioo
      hdiff_f hdiff_g hder hzero hinit
  exact hEq

/-- The two field components satisfy the actual physical frozen Kummer
second-order system along z0+t on the local existence interval. -/
theorem frozenKummer_local_physical_equation
    (mu theta z0 : ℝ) (u0 p0 : ℂ) (eps : ℝ)
    (heps : 0 < eps)
    (X : ℝ → KummerODEState)
    (hX0 : X 0 = (z0, (u0, p0)))
    (hODE : ∀ t ∈ Ioo (-eps) eps,
      HasDerivAt X (frozenKummerAugmentedField mu theta (X t)) t)
    (t : ℝ) (ht : t ∈ Ioo (-eps) eps) :
    HasDerivAt (fun s : ℝ => (X s).2.1) (X t).2.2 t ∧
    HasDerivAt (fun s : ℝ => (X s).2.2)
      (-(frozenFirstCoeff (z0 + t) * (X t).2.2 +
        frozenZeroCoeff mu theta * (X t).2.1)) t := by
  have h := frozenKummer_augmented_derivatives mu theta X (hODE t ht)
  rw [frozenKummer_trajectory_time_coordinate mu theta z0 u0 p0 eps
    heps X hX0 hODE t ht] at h
  exact ⟨h.2.1, h.2.2⟩

#print axioms frozenKummer_augmented_derivatives
#print axioms frozenKummer_trajectory_time_coordinate
#print axioms frozenKummer_local_physical_equation

end HBL.Profile.Kummer
