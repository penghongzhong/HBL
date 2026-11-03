import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleRadialDecay
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# Short exact measurability proof for the physical moving Hartree monopole

The original physical source has exactly
  V_c(r) = bubble(r) + c * monopoleInnerRadialProfile(R(c),r).
The continuous bubble and the already proved measurable truncated
Fredholm profile imply measurability immediately. No new source
regularity assumption, alternative cutoff, axiom, or blowup rate
is introduced. This replaces an unnecessary long proof via the
amplitude-dependent cutoff identity.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- True amplitude-dependent Hartree monopole is measurable, including
the origin and the c=0 case, by the already-certified decomposition. -/
theorem actual_Hartree_moving_monopole_measurable (c : ℝ) :
    Measurable
      (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c) := by
  unfold monopolePerturbedRadialProfile
  exact bubble_contDiff_infty.continuous.measurable.add
    (measurable_const.mul
      (monopoleInnerRadialProfile_measurable (monopoleQuadraticRadius c)))

end HBL.TypeIIDynamicSelection
