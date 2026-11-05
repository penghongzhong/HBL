import HBL.TypeIIDynamicSelection.ActualMixedQuarticCenterGain
import HBL.TypeIIDynamicSelection.ActualWholeRadiationSelfCubic
import Mathlib.Tactic

/-!
# Whole-radiation center mismatch after extracting the linear Fredholm source

The slow monopole coefficient is the exact whole-radiation self center.
Therefore the full Hartree interaction center does NOT require a separate
scalar exterior-mass fixed point.  After subtracting the real-linear mixed
charge (the part already sent to the Fredholm channels), only the quadratic
and higher mixed quartic center remains.

Under the existing physical amplitude and radial L2 bounds this remainder is
O(s^(-2 beta)), hence strictly integrable for beta > 1/2.  No stronger
beta > 2/3 condition is introduced.

This is a source-organization theorem.  It does not by itself construct the
Kummer-to-remote field or the final finite-profile iterate.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual Hartree center increment caused by adding the whole complex
radiation Z to a real profile V. -/
def actualWholeRadiationInteractionCenterIncrement
    (V : ℝ → ℝ) (Z : ℝ → ℂ) : ℝ :=
  radialHartreeCenter (fun rho => ‖(V rho : ℂ) + Z rho‖ ^ 4) -
    radialHartreeCenter (fun rho => ‖(V rho : ℂ)‖ ^ 4)

/-- Exact center bookkeeping:
full interaction increment = self-radiation center + linear mixed charge
+ quadratic/higher mixed charge. -/
theorem actual_whole_radiation_interaction_center_by_degree
    (V : ℝ → ℝ) (Z : ℝ → ℂ)
    (hFull : IntegrableOn
      (fun rho => ‖(V rho : ℂ) + Z rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hV : IntegrableOn
      (fun rho => ‖(V rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hZ : IntegrableOn
      (fun rho => ‖Z rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hLinear : IntegrableOn
      (fun rho => 4 * V rho ^ 3 * (Z rho).re) (Ioi (0 : ℝ)))
    (hHigher : IntegrableOn
      (actualWholeRadiationMixedHigher V Z) (Ioi (0 : ℝ))) :
    actualWholeRadiationInteractionCenterIncrement V Z =
      actualRadiationCenter Z +
        radialHartreeCenter (fun rho => 4 * V rho ^ 3 * (Z rho).re) +
        radialHartreeCenter (actualWholeRadiationMixedHigher V Z) := by
  have hMixed :=
    actual_whole_radiation_mixed_center_exact V Z hFull hV hZ
  have hDegree :=
    actual_whole_radiation_mixed_center_by_degree V Z hLinear hHigher
  unfold actualWholeRadiationInteractionCenterIncrement
  rw [hMixed, hDegree]
  ring

/-- Once the exact self-radiation center and the real-linear mixed Fredholm
source are removed, the scalar center mismatch is precisely the NEGATIVE
quadratic/higher mixed center. -/
theorem actual_whole_radiation_center_mismatch_reduces_to_higher
    (V : ℝ → ℝ) (Z : ℝ → ℂ)
    (hFull : IntegrableOn
      (fun rho => ‖(V rho : ℂ) + Z rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hV : IntegrableOn
      (fun rho => ‖(V rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hZ : IntegrableOn
      (fun rho => ‖Z rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hLinear : IntegrableOn
      (fun rho => 4 * V rho ^ 3 * (Z rho).re) (Ioi (0 : ℝ)))
    (hHigher : IntegrableOn
      (actualWholeRadiationMixedHigher V Z) (Ioi (0 : ℝ))) :
    actualRadiationCenter Z -
        actualWholeRadiationInteractionCenterIncrement V Z +
        radialHartreeCenter (fun rho => 4 * V rho ^ 3 * (Z rho).re) =
      -radialHartreeCenter (actualWholeRadiationMixedHigher V Z) := by
  rw [actual_whole_radiation_interaction_center_by_degree
    V Z hFull hV hZ hLinear hHigher]
  ring

/-- Quantitative version of the previous identity.  The only center error
left after the self-center and linear Fredholm source are extracted is
O(s^(-2 beta)), with positive time excess 2 beta - 1 for beta > 1/2. -/
theorem actual_whole_radiation_center_mismatch_twoBeta_gain
    (V : ℝ → ℝ) (Z : ℝ → ℂ)
    {s beta A CV CZ : ℝ}
    (hs : 1 ≤ s) (hbeta : (1 / 2 : ℝ) < beta)
    (hVmeas : Measurable V) (hZmeas : Measurable Z)
    (hV2 : IntegrableOn (fun rho => |V rho| ^ 2) (Ioi (0 : ℝ)))
    (hZ2 : IntegrableOn (fun rho => ‖Z rho‖ ^ 2) (Ioi (0 : ℝ)))
    (hVmass : (∫ rho in Ioi (0 : ℝ), |V rho| ^ 2) ≤ CV)
    (hZmass : (∫ rho in Ioi (0 : ℝ), ‖Z rho‖ ^ 2) ≤ CZ)
    (hZpoint : ∀ rho : ℝ, 0 < rho → ‖Z rho‖ ≤ A * s ^ (-beta))
    (hFull : IntegrableOn
      (fun rho => ‖(V rho : ℂ) + Z rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hV4 : IntegrableOn
      (fun rho => ‖(V rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hZ4 : IntegrableOn
      (fun rho => ‖Z rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hLinear : IntegrableOn
      (fun rho => 4 * V rho ^ 3 * (Z rho).re) (Ioi (0 : ℝ))) :
    0 < 2 * beta - 1 ∧
    |actualRadiationCenter Z -
        actualWholeRadiationInteractionCenterIncrement V Z +
        radialHartreeCenter (fun rho => 4 * V rho ^ 3 * (Z rho).re)| ≤
      (4 * Real.pi * hartreeKappa * A ^ 2 * (8 * CV + 2 * CZ)) *
        s ^ (-2 * beta) := by
  have hHigher :=
    actual_whole_radiation_mixed_center_uniformMass_twoBeta_gain
      V Z hs hbeta hVmeas hZmeas hV2 hZ2 hVmass hZmass hZpoint
  have hEq :=
    actual_whole_radiation_center_mismatch_reduces_to_higher
      V Z hFull hV4 hZ4 hLinear hHigher.2.1
  refine ⟨hHigher.1, ?_⟩
  rw [hEq, abs_neg]
  exact hHigher.2.2

end HBL.TypeIIDynamicSelection
