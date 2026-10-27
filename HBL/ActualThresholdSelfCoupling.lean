import HBL.CoupledThresholdMap
import Mathlib.Tactic

/-!
# Actual retained self-coupling coefficient

The exact triangular equation contains C(s)=ell(s) ∘ E(s), where ell is
the bounded threshold observation and E is the parameter-residual tangent.
This file records the elementary operator-norm passage from the already
verified E-decay to the finite-dimensional self-coupling decay.

No dynamical conclusion is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.MainBackward

def actualThresholdSelfCoupling
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ell : ℝ → X →L[ℝ] (ℝ × ℝ))
    (E : ℝ → (ℝ × ℝ) →L[ℝ] X)
    (s : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ell s).comp (E s)

theorem actualThresholdSelfCoupling_continuous
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ell : ℝ → X →L[ℝ] (ℝ × ℝ))
    (E : ℝ → (ℝ × ℝ) →L[ℝ] X)
    (hell : Continuous ell) (hE : Continuous E) :
    Continuous (actualThresholdSelfCoupling ell E) := by
  unfold actualThresholdSelfCoupling
  fun_prop

theorem actualThresholdSelfCoupling_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ell : ℝ → X →L[ℝ] (ℝ × ℝ))
    (E : ℝ → (ℝ × ℝ) →L[ℝ] X)
    (s0 nu Lell LE : ℝ)
    (hLell : 0 ≤ Lell) (hLE : 0 ≤ LE)
    (hell : ∀ t, s0 ≤ t → ‖ell t‖ ≤ Lell)
    (hE : ∀ t, s0 ≤ t → ‖E t‖ ≤ LE * t ^ (-nu)) :
    ∀ t, s0 ≤ t →
      ‖actualThresholdSelfCoupling ell E t‖ ≤
        (Lell * LE) * t ^ (-nu) := by
  intro t ht
  calc
    ‖actualThresholdSelfCoupling ell E t‖
        ≤ ‖ell t‖ * ‖E t‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Lell * (LE * t ^ (-nu)) :=
      mul_le_mul (hell t ht) (hE t ht) (norm_nonneg _)
        hLell
    _ = (Lell * LE) * t ^ (-nu) := by ring

/-- The actual self-coupling therefore has a late-time contraction constant
tending to zero whenever the residual tangent decays with exponent nu>2. -/
theorem actualThresholdSelfCoupling_small_at_late_time
    (p nu Lell LE : ℝ) (hnu : 2 < nu) :
    Tendsto
      (fun s0 : ℝ =>
        thresholdSelfLipschitzConstant s0 p nu (Lell * LE))
      Filter.atTop (𝓝 0) :=
  thresholdSelfLipschitzConstant_tendsto_zero p nu (Lell * LE) hnu

#print axioms actualThresholdSelfCoupling_continuous
#print axioms actualThresholdSelfCoupling_bound
#print axioms actualThresholdSelfCoupling_small_at_late_time

end HBL.MainBackward
