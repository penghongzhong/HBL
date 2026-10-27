import HBL.StrongConstrainedCenterEvolution
import HBL.WeightedThresholdMap
import HBL.WeightedCenterNonlinearMap
import HBL.WeightedAffineForcing
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Strong dynamics of the weighted backward tails

Unnumbered bridge for the final HBL main theorem.

The threshold terminal integral is differentiated natively in Lean.
For the infinite-dimensional centre equation we use only the explicit
Kato--Kisyński strong-evolution boundary isolated in
`StrongConstrainedCenterEvolution.lean`.

No fixed point, shooting graph, blow-up solution, or final rate is assumed.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.MainBackward

/-- A continuous Bochner tail has the expected strong derivative:
d/ds[-∫_s^∞ F(t)dt] = F(s). -/
theorem neg_Ioi_integral_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) {s0 s : ℝ}
    (hF : Continuous F) (hInt : IntegrableOn F (Ioi s0))
    (hs : s0 < s) :
    HasDerivAt (fun x => -(∫ t in Ioi x, F t)) (F s) s := by
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hF.intervalIntegrable s0 s)
    hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have hm :
      HasDerivAt
        (fun x => (∫ t in s0..x, F t) - ∫ t in Ioi s0, F t)
        (F s) s :=
    hd.sub_const (∫ t in Ioi s0, F t)
  apply hm.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with x hx
  have hi := intervalIntegral.integral_interval_add_Ioi hInt
    (hInt.mono_set (Ioi_subset_Ioi hx.le))
  rw [← hi]
  abel

/-- The actual retained threshold tail satisfies its terminal ODE. -/
theorem weightedThresholdTail_hasDerivAt
    (B : ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ))
    (s0 p : ℝ) (hs0 : 0 < s0) (hp : 1 < p)
    (q : CenterWeightedPath s0 p) {s : ℝ} (hs : s0 < s) :
    HasDerivAt (weightedThresholdTail B s0 p q)
      (weightedThresholdSource B s0 p q s) s := by
  have hF := weightedThresholdSource_continuous B s0 p hs0 q
  have hInt := weightedThresholdSource_integrable B s0 p hs0 hp q
  simpa only [weightedThresholdTail] using
    (neg_Ioi_integral_hasDerivAt
      (weightedThresholdSource B s0 p q) hF hInt hs)

/-- The finite-profile threshold forcing tail has the same exact derivative. -/
theorem weightedThresholdForcingTail_hasDerivAt
    (F : ℝ → ℝ × ℝ) {s0 s : ℝ}
    (hF : Continuous F) (hInt : IntegrableOn F (Ioi s0))
    (hs : s0 < s) :
    HasDerivAt (weightedThresholdForcingTail F) (F s) s := by
  simpa only [weightedThresholdForcingTail] using
    (neg_Ioi_integral_hasDerivAt F hF hInt hs)

/-- Strong centre equation for the retained threshold feedback tail. -/
theorem weightedCenterFeedbackTail_strong
    {s0 p nu L : ℝ}
    (S : StrongConstrainedCenterPropagator s0)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hL : 0 ≤ L) (hEcont : Continuous E)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (a : ThresholdWeightedPath s0 p)
    {s : ℝ} (hs : s0 < s) :
    ∃ hdom :
      constrainedCenterEmbedding
          (weightedCenterFeedbackTail S.standard E p a s) ∈ S.domain,
      HasDerivAt
        (fun r => constrainedCenterEmbedding
          (weightedCenterFeedbackTail S.standard E p a r))
        (S.generator s
            ⟨constrainedCenterEmbedding
              (weightedCenterFeedbackTail S.standard E p a s), hdom⟩ +
          constrainedCenterEmbedding
            (E s (unweightThresholdPathGlobal s0 p a s)))
        s := by
  let F : ℝ → ConstrainedCenterSpace :=
    fun t => E t (unweightThresholdPathGlobal s0 p a t)
  have hFcont : Continuous F :=
    weightedCenterPrimitiveSource_continuous E p hs0 hEcont a
  have hInt : ∀ r, s0 ≤ r →
      IntegrableOn (fun t => S.standard.U r t (F t)) (Ioi r) := by
    intro r hr
    simpa only [F, weightedCenterFeedbackSource] using
      (weightedCenterFeedbackSource_integrable
        S.standard E hs0 hp hnu hL hEcont hE a hr)
  simpa only [F, centerDuhamelTail, weightedCenterFeedbackTail,
    weightedCenterFeedbackSource] using
    (strongCenterDuhamel_certified S F hFcont hInt hs)

/-- Strong centre equation for the genuine nonlinear Duhamel tail. -/
theorem weightedCenterNonlinearTail_strong
    {s0 p delta Cnl : ℝ}
    (S : StrongConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCnl : 0 ≤ Cnl)
    (hGcont : Continuous
      (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hGzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hGlip : ∀ t, s0 ≤ t → ∀ z w,
      ‖G t z - G t w‖ ≤
        Cnl * t ^ (-1 - delta) * ‖z - w‖)
    (q : CenterWeightedPath s0 p)
    {s : ℝ} (hs : s0 < s) :
    ∃ hdom :
      constrainedCenterEmbedding
          (weightedCenterNonlinearTail S.standard G p q s) ∈ S.domain,
      HasDerivAt
        (fun r => constrainedCenterEmbedding
          (weightedCenterNonlinearTail S.standard G p q r))
        (S.generator s
            ⟨constrainedCenterEmbedding
              (weightedCenterNonlinearTail S.standard G p q s), hdom⟩ +
          constrainedCenterEmbedding
            (G s (unweightPathGlobal p s0 q s)))
        s := by
  let F : ℝ → ConstrainedCenterSpace :=
    fun t => G t (unweightPathGlobal p s0 q t)
  have hFcont : Continuous F := by
    exact hGcont.comp
      (continuous_id.prodMk
        (unweightPathGlobal_continuous p s0 hs0 q))
  have hInt : ∀ r, s0 ≤ r →
      IntegrableOn (fun t => S.standard.U r t (F t)) (Ioi r) := by
    intro r hr
    simpa only [F, weightedCenterNonlinearSource] using
      (weightedCenterNonlinearSource_integrable
        S.standard G hs0 hp hdelta hCnl hGcont hGzero hGlip q hr)
  simpa only [F, centerDuhamelTail, weightedCenterNonlinearTail,
    weightedCenterNonlinearSource] using
    (strongCenterDuhamel_certified S F hFcont hInt hs)

/-- Strong centre equation for the fixed high-order profile forcing tail. -/
theorem weightedCenterForcingTail_strong
    {s0 : ℝ}
    (S : StrongConstrainedCenterPropagator s0)
    (F : ℝ → ConstrainedCenterSpace)
    (p N CF : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hN : p + 1 < N)
    (hCF : 0 ≤ CF) (hFcont : Continuous F)
    (hF : ∀ t, s0 ≤ t → ‖F t‖ ≤ CF * t ^ (-N))
    {s : ℝ} (hs : s0 < s) :
    ∃ hdom :
      constrainedCenterEmbedding
          (weightedCenterForcingTail S.standard F s) ∈ S.domain,
      HasDerivAt
        (fun r => constrainedCenterEmbedding
          (weightedCenterForcingTail S.standard F r))
        (S.generator s
            ⟨constrainedCenterEmbedding
              (weightedCenterForcingTail S.standard F s), hdom⟩ +
          constrainedCenterEmbedding (F s))
        s := by
  have hInt : ∀ r, s0 ≤ r →
      IntegrableOn (fun t => S.standard.U r t (F t)) (Ioi r) := by
    intro r hr
    have hrpos : 0 < r := hs0.trans_le hr
    have hmajor : IntegrableOn
        (fun t : ℝ => (S.standard.boundConst * CF) * t ^ (-N)) (Ioi r) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hrpos).const_mul _
    have hmeas :
        AEStronglyMeasurable (fun t => S.standard.U r t (F t))
          (volume.restrict (Ioi r)) :=
      (S.standard.orbit_continuous r F hFcont).aestronglyMeasurable.restrict
    apply hmajor.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      ‖S.standard.U r t (F t)‖
          ≤ ‖S.standard.U r t‖ * ‖F t‖ :=
            (S.standard.U r t).le_opNorm _
      _ ≤ S.standard.boundConst * (CF * t ^ (-N)) := by
        exact mul_le_mul
          (S.standard.bound r t hr ht.le)
          (hF t (hr.trans ht.le))
          (norm_nonneg _) S.standard.bound_nonneg
      _ = (S.standard.boundConst * CF) * t ^ (-N) := by ring
  simpa only [centerDuhamelTail, weightedCenterForcingTail] using
    (strongCenterDuhamel_certified S F hFcont hInt hs)

#print axioms neg_Ioi_integral_hasDerivAt
#print axioms weightedThresholdTail_hasDerivAt
#print axioms weightedThresholdForcingTail_hasDerivAt
#print axioms weightedCenterFeedbackTail_strong
#print axioms weightedCenterNonlinearTail_strong
#print axioms weightedCenterForcingTail_strong

end HBL.MainBackward
