import HBL.FiniteRadialModulation
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
Tail-insensitive lifting of the finite-radius modulation theorem.

The two compact orthogonality tests only see the finite radial-energy
coordinate on (0,R).  Therefore the modulation theorem remains valid
after adjoining an arbitrary complete real Banach tail space T: the
test functionals are precomposed with projection to the finite component.

This isolates the last manuscript-level issue to the identification of
the full radial homogeneous energy space with a finite core plus tail.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

section LiftedDual

variable {V T : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- Lift a finite-coordinate functional so that it ignores an arbitrary tail. -/
def liftFiniteDual (ell : V →L[ℝ] ℝ) : (V × T) →L[ℝ] ℝ :=
  ell.comp (ContinuousLinearMap.fst ℝ V T)

@[simp]
theorem liftFiniteDual_apply (ell : V →L[ℝ] ℝ) (v : V) (t : T) :
    liftFiniteDual (T := T) ell (v, t) = ell v := by
  rfl

/-- Precomposition by the finite-coordinate projection is itself bounded
linear on operator spaces. -/
def liftFiniteDualCLM : (V →L[ℝ] ℝ) →L[ℝ] ((V × T) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (V × T) V ℝ).flip
    (ContinuousLinearMap.fst ℝ V T)

@[simp]
theorem liftFiniteDualCLM_apply (ell : V →L[ℝ] ℝ) :
    liftFiniteDualCLM (V := V) (T := T) ell =
      liftFiniteDual (T := T) ell := by
  rfl

/-- C1 operator-norm dependence survives adjoining an ignored tail space. -/
theorem liftFiniteDual_contDiffAt
    (S : ℝ → (V →L[ℝ] ℝ))
    (hS : ContDiffAt ℝ 1 S (0 : ℝ)) :
    ContDiffAt ℝ 1
      (fun a : ℝ => liftFiniteDual (T := T) (S a)) 0 := by
  change ContDiffAt ℝ 1
    (fun a : ℝ => liftFiniteDualCLM (V := V) (T := T) (S a)) 0
  exact (liftFiniteDualCLM (V := V) (T := T)).contDiff.contDiffAt.comp 0 hS

end LiftedDual

section TailLiftedModulation

variable {T : Type*}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- The compact-test modulation theorem is unchanged after adjoining any
complete Banach tail.  In particular, the far radial energy can be kept
without entering the two orthogonality equations. -/
theorem finiteRadialEnergy_local_modulation_with_tail
    (R : ℝ) (hR : 0 ≤ R)
    (zPlus zMinus : ℝ → ℝ)
    (hzPlus : ContDiff ℝ 1 zPlus)
    (hzMinus : ContDiff ℝ 1 zMinus)
    (hzPlusR : zPlus R = 0)
    (hPlusNorm :
      (∫ r in (0 : ℝ)..R,
        zPlus r * radialResonancePlus r) = 1)
    (hMinusNorm :
      (∫ r in (0 : ℝ)..R,
        zMinus r * radialResonanceMinus r) = 1)
    (tailBubble : T) :
    ∃ Phi :
      ((RadialEnergyL2 R × T) × (RadialEnergyL2 R × T)) → Param,
      Phi ((bubbleRadialEnergyL2 R hR, tailBubble),
        (0 : RadialEnergyL2 R × T)) = (1, 0) ∧
      ContDiffAt ℝ 1 Phi
        ((bubbleRadialEnergyL2 R hR, tailBubble),
          (0 : RadialEnergyL2 R × T)) ∧
      (∀ u, 0 < (Phi u).1) ∧
      (∀ᶠ u in 𝓝
        ((bubbleRadialEnergyL2 R hR, tailBubble),
          (0 : RadialEnergyL2 R × T)),
        scalePhaseResidual
          (fun a => liftFiniteDual (T := T)
            (transportedEnergyThresholdDual R hR zPlus hzPlus a))
          (fun a => liftFiniteDual (T := T)
            (transportedEnergyThresholdDual R hR zMinus hzMinus a))
          (bubbleRadialEnergyL2 R hR, tailBubble)
          (u, (Real.log (Phi u).1, (Phi u).2)) = 0) ∧
      (∀ᶠ v in 𝓝
        (((bubbleRadialEnergyL2 R hR, tailBubble),
            (0 : RadialEnergyL2 R × T)),
          (0 : Param)),
        (scalePhaseResidual
          (fun a => liftFiniteDual (T := T)
            (transportedEnergyThresholdDual R hR zPlus hzPlus a))
          (fun a => liftFiniteDual (T := T)
            (transportedEnergyThresholdDual R hR zMinus hzMinus a))
          (bubbleRadialEnergyL2 R hR, tailBubble) v = 0 ↔
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2)) := by
  let Splus : ℝ → ((RadialEnergyL2 R × T) →L[ℝ] ℝ) :=
    fun a => liftFiniteDual (T := T)
      (transportedEnergyThresholdDual R hR zPlus hzPlus a)
  let Sminus : ℝ → ((RadialEnergyL2 R × T) →L[ℝ] ℝ) :=
    fun a => liftFiniteDual (T := T)
      (transportedEnergyThresholdDual R hR zMinus hzMinus a)
  let w : RadialEnergyL2 R × T :=
    (bubbleRadialEnergyL2 R hR, tailBubble)
  have hPlusC1 :
      ContDiffAt ℝ 1 Splus 0 := by
    exact liftFiniteDual_contDiffAt
      (T := T)
      (transportedEnergyThresholdDual R hR zPlus hzPlus)
      (transportedEnergyThresholdDual_contDiffAt_zero
        R hR zPlus hzPlus)
  have hMinusC1 :
      ContDiffAt ℝ 1 Sminus 0 := by
    exact liftFiniteDual_contDiffAt
      (T := T)
      (transportedEnergyThresholdDual R hR zMinus hzMinus)
      (transportedEnergyThresholdDual_contDiffAt_zero
        R hR zMinus hzMinus)
  have hScale :
      HasDerivAt (fun a : ℝ => Splus a w) (-1) 0 := by
    have h :=
      transportedEnergyThresholdDual_bubble_hasDerivAt
        R hR zPlus hzPlus hzPlusR hPlusNorm
    simpa [Splus, w, bubbleRadialEnergyL2, liftFiniteDual] using h
  have hPhase :
      Sminus 0 w = 1 := by
    have h :=
      transportedEnergyThresholdDual_bubble_zero_eq_one
        R hR zMinus hzMinus hMinusNorm
    simpa [Sminus, w, bubbleRadialEnergyL2, liftFiniteDual] using h
  simpa [Splus, Sminus, w] using
    scalePhase_local_modulation_physical Splus Sminus w
      hPlusC1 hMinusC1 hScale hPhase

end TailLiftedModulation

end HBL.Modulation
