import HBL.WeightedCenterFeedbackMap
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Standard strong constrained-centre evolution boundary

Literature-level Kato--Kisyński interface for the nonautonomous linear
centre equation on a common form/generator domain.  The propagator acts on
the actual closed HBL constrained centre space, while the strong equation is
read in the ambient two-channel energy space.

This is an external analysis boundary only.  It contains no HBL blow-up
orbit, nonlinear fixed point, shooting graph, rate selection, or manuscript
main-theorem conclusion.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.MainBackward

/-- Continuous inclusion of the actual constrained centre space into the
ambient two-channel energy space. -/
def constrainedCenterEmbedding : ConstrainedCenterSpace →L[ℝ] CenterPair :=
  Submodule.subtypeL constrainedCenterSubmodule

/-- Backward Duhamel tail associated with the standard constrained
propagator. -/
def centerDuhamelTail {s0 : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (F : ℝ → ConstrainedCenterSpace) (s : ℝ) : ConstrainedCenterSpace :=
  -(∫ t in Ioi s, CE.U s t (F t))

/-- Strong Kato--Kisyński output on the common generator domain.
For every continuous tail-integrable source, the backward Duhamel tail lies
in the common domain and satisfies z_s = A(s)z + F(s). -/
structure StrongConstrainedCenterPropagator (s0 : ℝ) where
  standard : StandardConstrainedCenterPropagator s0
  domain : Submodule ℝ CenterPair
  generator : ℝ → domain →ₗ[ℝ] CenterPair
  tail_strong :
    ∀ (F : ℝ → ConstrainedCenterSpace),
      Continuous F →
      (∀ r, s0 ≤ r →
        IntegrableOn (fun t => standard.U r t (F t)) (Ioi r)) →
      ∀ s, s0 < s →
        ∃ hdom :
          constrainedCenterEmbedding (centerDuhamelTail standard F s) ∈ domain,
          HasDerivAt
            (fun r =>
              constrainedCenterEmbedding (centerDuhamelTail standard F r))
            (generator s
                ⟨constrainedCenterEmbedding (centerDuhamelTail standard F s),
                  hdom⟩ +
              constrainedCenterEmbedding (F s))
            s

/-- The strong boundary in particular provides the required domain
membership and strong derivative for each Duhamel tail. -/
theorem strongCenterDuhamel_certified
    {s0 : ℝ} (S : StrongConstrainedCenterPropagator s0)
    (F : ℝ → ConstrainedCenterSpace)
    (hF : Continuous F)
    (hInt : ∀ r, s0 ≤ r →
      IntegrableOn (fun t => S.standard.U r t (F t)) (Ioi r))
    {s : ℝ} (hs : s0 < s) :
    ∃ hdom :
      constrainedCenterEmbedding (centerDuhamelTail S.standard F s) ∈ S.domain,
      HasDerivAt
        (fun r =>
          constrainedCenterEmbedding (centerDuhamelTail S.standard F r))
        (S.generator s
            ⟨constrainedCenterEmbedding (centerDuhamelTail S.standard F s),
              hdom⟩ +
          constrainedCenterEmbedding (F s))
        s :=
  S.tail_strong F hF hInt s hs

#print axioms constrainedCenterEmbedding
#print axioms centerDuhamelTail
#print axioms strongCenterDuhamel_certified

end HBL.MainBackward
