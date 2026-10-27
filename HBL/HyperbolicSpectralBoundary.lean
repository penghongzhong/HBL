import HBL.UnstableShootingTerminal
import HBL.CenterCoercivity
import Mathlib.Tactic

/-!
# Fixed-bubble hyperbolic spectral boundary and moving-rate bridge

Literature boundary for the radial generalized energy-critical Hartree
linearized Hamiltonian at the fixed bubble.  Proposition 2.14 of
Li--Liu--Tang--Xu gives radial eigenmodes with real eigenvalues ±e0,
e0>0, together with coercivity away from the symmetry/hyperbolic directions.
The present interface keeps only the exact piece needed by the HBL shooting
argument: a bounded growth coordinate whose derivative under the fixed
linearized generator is multiplication by e0.

No HBL shooting solution, moving profile, nonlinear source, or main-theorem
conclusion is included in this external input.
-/

noncomputable section
set_option autoImplicit false

open scoped Topology

namespace HBL.MainBackward

/-- Minimal literature-level fixed-bubble hyperbolic spectral output. -/
structure FixedBubbleHyperbolicSpectralBoundary where
  domain : Submodule ℝ CenterPair
  generator : domain →ₗ[ℝ] CenterPair
  e0 : ℝ
  e0_pos : 0 < e0
  growthCoordinate : CenterPair →L[ℝ] ℝ
  decayCoordinate : CenterPair →L[ℝ] ℝ
  growth_generator :
    ∀ v : domain,
      growthCoordinate (generator v) = e0 * growthCoordinate v.1
  decay_generator :
    ∀ v : domain,
      decayCoordinate (generator v) = -e0 * decayCoordinate v.1

/-- The fixed Hamiltonian growth coordinate satisfies the scalar e0 equation
for every strong trajectory in the common domain. -/
theorem fixedBubble_growthCoordinate_hasDerivAt
    (S : FixedBubbleHyperbolicSpectralBoundary)
    (v F : ℝ → CenterPair) (s : ℝ)
    (hvdom : v s ∈ S.domain)
    (hv : HasDerivAt v (S.generator ⟨v s, hvdom⟩ + F s) s) :
    HasDerivAt (fun t => S.growthCoordinate (v t))
      (S.e0 * S.growthCoordinate (v s) + S.growthCoordinate (F s)) s := by
  have h := S.growthCoordinate.hasFDerivAt.comp_hasDerivAt s hv
  convert h using 1
  rw [map_add, S.growth_generator]

/-- The fixed Hamiltonian decay coordinate satisfies the scalar -e0 equation. -/
theorem fixedBubble_decayCoordinate_hasDerivAt
    (S : FixedBubbleHyperbolicSpectralBoundary)
    (v F : ℝ → CenterPair) (s : ℝ)
    (hvdom : v s ∈ S.domain)
    (hv : HasDerivAt v (S.generator ⟨v s, hvdom⟩ + F s) s) :
    HasDerivAt (fun t => S.decayCoordinate (v t))
      (-S.e0 * S.decayCoordinate (v s) + S.decayCoordinate (F s)) s := by
  have h := S.decayCoordinate.hasFDerivAt.comp_hasDerivAt s hv
  convert h using 1
  rw [map_add, S.decay_generator]

/-- Algebraic splitting of the moving perturbation into a correction to the
hyperbolic rate and the projected total source. -/
theorem moving_growthCoordinate_hasDerivAt
    (S : FixedBubbleHyperbolicSpectralBoundary)
    (v H : ℝ → CenterPair) (delta f : ℝ → ℝ) (s : ℝ)
    (hvdom : v s ∈ S.domain)
    (hv : HasDerivAt v (S.generator ⟨v s, hvdom⟩ + H s) s)
    (hproj :
      S.growthCoordinate (H s) =
        delta s * S.growthCoordinate (v s) + f s) :
    HasDerivAt (fun t => S.growthCoordinate (v t))
      ((S.e0 + delta s) * S.growthCoordinate (v s) + f s) s := by
  have h := fixedBubble_growthCoordinate_hasDerivAt S v H s hvdom hv
  convert h using 1
  rw [hproj]
  ring

/-- A small moving correction preserves half of the fixed hyperbolic gap. -/
theorem moving_hyperbolic_rate_lower
    (S : FixedBubbleHyperbolicSpectralBoundary)
    (delta : ℝ → ℝ) {s : ℝ}
    (hdelta : |delta s| ≤ S.e0 / 2) :
    S.e0 / 2 ≤ S.e0 + delta s := by
  have hlo : -(S.e0 / 2) ≤ delta s := (abs_le.mp hdelta).1
  linarith

theorem moving_hyperbolic_half_gap_pos
    (S : FixedBubbleHyperbolicSpectralBoundary) :
    0 < S.e0 / 2 := by
  linarith [S.e0_pos]

/-- Boundedness of the actual spectral projection converts any vector source
bound into the scalar source bound used by terminal shooting. -/
theorem growthCoordinate_source_bound
    (S : FixedBubbleHyperbolicSpectralBoundary)
    (F : CenterPair) :
    |S.growthCoordinate F| ≤ ‖S.growthCoordinate‖ * ‖F‖ := by
  simpa only [Real.norm_eq_abs] using S.growthCoordinate.le_opNorm F

#print axioms fixedBubble_growthCoordinate_hasDerivAt
#print axioms fixedBubble_decayCoordinate_hasDerivAt
#print axioms moving_growthCoordinate_hasDerivAt
#print axioms moving_hyperbolic_rate_lower
#print axioms growthCoordinate_source_bound

end HBL.MainBackward
