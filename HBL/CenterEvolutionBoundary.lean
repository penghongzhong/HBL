import HBL.PropagatedFeedbackTail

/-!
# Standard constrained centre evolution boundary

This is an unnumbered external analysis interface, analogous to the standard
high-regularity generalized-Hartree local-theory boundary used elsewhere in
the HBL verification.

Its mathematical source is standard nonautonomous evolution theory on a
constant coercive form domain (Kato--Kisyński).  The HBL-specific coercive
form and its moving perturbation are verified in the physical energy modules.
The interface itself does not assert a blow-up orbit, a shooting graph, or
any manuscript conclusion.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.MainBackward

/-- Standard output of the constrained linear centre evolution. -/
structure StandardConstrainedCenterEvolution where
  U : ℝ → ℝ → CenterEnergySpace →L[ℝ] CenterEnergySpace
  boundConst : ℝ
  boundConst_nonneg : 0 ≤ boundConst
  bound : ∀ s t : ℝ, s ≤ t → ‖U s t‖ ≤ boundConst
  continuous_action :
    ∀ s : ℝ, Continuous (fun p : ℝ × CenterEnergySpace => U s p.1 p.2)

/-- Continuity, hence strong measurability, of a propagated continuous source. -/
theorem propagated_source_measurable
    (CE : StandardConstrainedCenterEvolution)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] CenterEnergySpace)
    (a b : ℝ → ℝ × ℝ)
    (hE : Continuous E) (ha : Continuous a) (hb : Continuous b)
    (s : ℝ) :
    AEStronglyMeasurable
      (fun t => CE.U s t (E t (a t - b t)))
      (volume.restrict (Ioi s)) := by
  have hs : Continuous (fun t => E t (a t - b t)) :=
    hE.clm_apply (ha.sub hb)
  have hp : Continuous (fun t => (t, E t (a t - b t))) :=
    continuous_id.prod_mk hs
  exact ((CE.continuous_action s).comp hp).aestronglyMeasurable.restrict

/-- The standard centre-evolution boundary and the verified feedback source
give the exact weighted Lipschitz constant used by the joint fixed point. -/
theorem standardCenter_feedback_lipschitz
    (CE : StandardConstrainedCenterEvolution)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] CenterEnergySpace)
    (a b : ℝ → ℝ × ℝ)
    (s0 p nu L D s : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hs : s0 ≤ s)
    (hEcont : Continuous E) (hacont : Continuous a) (hbcont : Continuous b)
    (hE : ∀ t, s ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (hab : ∀ t, s ≤ t → ‖a t - b t‖ ≤ D * t ^ (1 - p)) :
    ‖propagatedFeedbackTail CE.U E a b s‖ ≤
      ((CE.boundConst * L) / (p + nu - 2) * s0 ^ (2 - nu)) *
        D * s ^ (-p) := by
  exact propagatedFeedbackTail_difference_weighted
    CE.U E a b s0 p nu CE.boundConst L D s
    hs0 hp hnu CE.boundConst_nonneg hL hD hs
    (fun t hst => CE.bound s t hst)
    hE hab
    (propagated_source_measurable CE E a b hEcont hacont hbcont s)

#print axioms propagated_source_measurable
#print axioms standardCenter_feedback_lipschitz

end HBL.MainBackward
