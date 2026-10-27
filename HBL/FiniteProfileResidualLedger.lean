import HBL.FiniteProfile
import Mathlib.Tactic

/-!
# Finite-profile residual ledger

Unnumbered bookkeeping for the final HBL construction.

The accepted finite-profile environment proves that only finitely many
generated atoms remain and that their orders cross any prescribed fixed
threshold.  This file records the normed-space consequence used by the
backward problem: a finite sum of atoms of order at least N has an s^{-N}
bound, and the same is true for parameter differences.

No PDE orbit, propagator, or shooting conclusion is assumed.
-/

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology

namespace HBL.Profile.ResidualLedger

variable {E : Type*} [NormedAddCommGroup E]

/-- One realized residual atom with its actual weighted norm bound. -/
structure WeightedResidualAtom (E : Type*) [NormedAddCommGroup E] where
  value : ℝ → E
  order : ℝ
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound : ∀ s : ℝ, 1 ≤ s → ‖value s‖ ≤ constant * s ^ (-order)

/-- The finite residual represented by a list of realized atoms. -/
def residualSum (atoms : List (WeightedResidualAtom E)) (s : ℝ) : E :=
  (atoms.map (fun a => a.value s)).sum

/-- Sum of the nonnegative atom constants. -/
def residualConstant (atoms : List (WeightedResidualAtom E)) : ℝ :=
  (atoms.map (fun a => a.constant)).sum

theorem residualConstant_nonneg (atoms : List (WeightedResidualAtom E)) :
    0 ≤ residualConstant atoms := by
  induction atoms with
  | nil =>
      simp [residualConstant]
  | cons a atoms ih =>
      simp only [residualConstant, List.map_cons, List.sum_cons]
      exact add_nonneg a.constant_nonneg ih

/-- A finite residual whose atom orders are all at least N is O(s^{-N}). -/
theorem residualSum_bound_of_orders
    (atoms : List (WeightedResidualAtom E)) (N s : ℝ)
    (hN : ∀ a ∈ atoms, N ≤ a.order)
    (hs : 1 ≤ s) :
    ‖residualSum atoms s‖ ≤ residualConstant atoms * s ^ (-N) := by
  induction atoms with
  | nil =>
      simp [residualSum, residualConstant]
  | cons a atoms ih =>
      have haN : N ≤ a.order := hN a (by simp)
      have htailN : ∀ b ∈ atoms, N ≤ b.order := by
        intro b hb
        exact hN b (by simp [hb])
      have hp : s ^ (-a.order) ≤ s ^ (-N) :=
        Real.rpow_le_rpow_of_exponent_le hs (neg_le_neg haN)
      have ha : ‖a.value s‖ ≤ a.constant * s ^ (-N) :=
        (a.bound s hs).trans
          (mul_le_mul_of_nonneg_left hp a.constant_nonneg)
      have ht := ih htailN
      simp only [residualSum, residualConstant, List.map_cons, List.sum_cons] at ht ⊢
      calc
        ‖a.value s + (atoms.map (fun b => b.value s)).sum‖
            ≤ ‖a.value s‖ + ‖(atoms.map (fun b => b.value s)).sum‖ :=
              norm_add_le _ _
        _ ≤ a.constant * s ^ (-N) +
              (atoms.map (fun b => b.constant)).sum * s ^ (-N) :=
              add_le_add ha ht
        _ = (a.constant + (atoms.map (fun b => b.constant)).sum) *
              s ^ (-N) := by ring

variable {P : Type*} [NormedAddCommGroup P]

/-- A realized residual atom with an actual parameter-difference estimate. -/
structure ParametricResidualAtom
    (P : Type*) [NormedAddCommGroup P]
    (E : Type*) [NormedAddCommGroup E] where
  value : P → ℝ → E
  order : ℝ
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  lipschitz :
    ∀ theta eta : P, ∀ s : ℝ, 1 ≤ s →
      ‖value theta s - value eta s‖ ≤
        constant * s ^ (-order) * ‖theta - eta‖

def parametricResidualSum
    (atoms : List (ParametricResidualAtom P E)) (theta : P) (s : ℝ) : E :=
  (atoms.map (fun a => a.value theta s)).sum

def parametricResidualConstant
    (atoms : List (ParametricResidualAtom P E)) : ℝ :=
  (atoms.map (fun a => a.constant)).sum

theorem parametricResidualConstant_nonneg
    (atoms : List (ParametricResidualAtom P E)) :
    0 ≤ parametricResidualConstant atoms := by
  induction atoms with
  | nil =>
      simp [parametricResidualConstant]
  | cons a atoms ih =>
      simp only [parametricResidualConstant, List.map_cons, List.sum_cons]
      exact add_nonneg a.constant_nonneg ih

/-- Finite parameter differences inherit the minimum residual order. -/
theorem parametricResidualSum_difference_bound
    (atoms : List (ParametricResidualAtom P E))
    (N s : ℝ) (theta eta : P)
    (hN : ∀ a ∈ atoms, N ≤ a.order)
    (hs : 1 ≤ s) :
    ‖parametricResidualSum atoms theta s -
        parametricResidualSum atoms eta s‖ ≤
      parametricResidualConstant atoms * s ^ (-N) * ‖theta - eta‖ := by
  induction atoms with
  | nil =>
      simp [parametricResidualSum, parametricResidualConstant]
  | cons a atoms ih =>
      have haN : N ≤ a.order := hN a (by simp)
      have htailN : ∀ b ∈ atoms, N ≤ b.order := by
        intro b hb
        exact hN b (by simp [hb])
      have hp : s ^ (-a.order) ≤ s ^ (-N) :=
        Real.rpow_le_rpow_of_exponent_le hs (neg_le_neg haN)
      have hnorm : 0 ≤ ‖theta - eta‖ := norm_nonneg _
      have ha0 := a.lipschitz theta eta s hs
      have ha : ‖a.value theta s - a.value eta s‖ ≤
          a.constant * s ^ (-N) * ‖theta - eta‖ := by
        exact ha0.trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp a.constant_nonneg) hnorm)
      have ht := ih htailN
      simp only [parametricResidualSum, parametricResidualConstant,
        List.map_cons, List.sum_cons] at ht ⊢
      have hsplit :
          (a.value theta s + (atoms.map (fun b => b.value theta s)).sum) -
            (a.value eta s + (atoms.map (fun b => b.value eta s)).sum) =
          (a.value theta s - a.value eta s) +
            ((atoms.map (fun b => b.value theta s)).sum -
              (atoms.map (fun b => b.value eta s)).sum) := by
        abel
      rw [hsplit]
      calc
        ‖(a.value theta s - a.value eta s) +
            ((atoms.map (fun b => b.value theta s)).sum -
              (atoms.map (fun b => b.value eta s)).sum)‖
            ≤ ‖a.value theta s - a.value eta s‖ +
                ‖(atoms.map (fun b => b.value theta s)).sum -
                  (atoms.map (fun b => b.value eta s)).sum‖ :=
              norm_add_le _ _
        _ ≤ a.constant * s ^ (-N) * ‖theta - eta‖ +
              (atoms.map (fun b => b.constant)).sum * s ^ (-N) *
                ‖theta - eta‖ :=
              add_le_add ha ht
        _ = (a.constant + (atoms.map (fun b => b.constant)).sum) *
              s ^ (-N) * ‖theta - eta‖ := by ring

/-- The preceding global finite-list estimate is in particular a local
Lipschitz estimate at every parameter value. -/
theorem parametricResidualSum_eventually_lipschitz
    (atoms : List (ParametricResidualAtom P E))
    (N s : ℝ) (theta : P)
    (hN : ∀ a ∈ atoms, N ≤ a.order)
    (hs : 1 ≤ s) :
    ∀ᶠ eta in 𝓝 theta,
      ‖parametricResidualSum atoms eta s -
          parametricResidualSum atoms theta s‖ ≤
        (parametricResidualConstant atoms * s ^ (-N)) *
          ‖eta - theta‖ := by
  filter_upwards [] with eta
  simpa only [mul_assoc] using
    parametricResidualSum_difference_bound atoms N s eta theta hN hs

#print axioms residualSum_bound_of_orders
#print axioms parametricResidualSum_difference_bound
#print axioms parametricResidualSum_eventually_lipschitz

end HBL.Profile.ResidualLedger
