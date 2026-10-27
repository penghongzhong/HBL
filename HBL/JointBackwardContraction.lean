import HBL.RetainedFeedbackTail
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Two-stage backward contraction

This is a generic Banach fixed-point lemma for the repaired HBL backward
scheme.  It is not a new manuscript theorem environment.

The threshold reconstruction maps a centre path to a finite-dimensional
terminal path, and the centre reconstruction maps that terminal path back
to the centre.  Once the two Lipschitz constants have product < 1, the
coupled pair exists and is unique.
-/

noncomputable section
set_option autoImplicit false

open Function Filter Set
open scoped Topology

namespace HBL.MainBackward


/-- Product of the one-power-loss threshold Lipschitz constant and the
late-time feedback-tail constant. -/
def jointBackwardProduct (p nu CU L B s : ℝ) : ℝ :=
  (B / (p - 1)) * ((CU * L) / (p + nu - 2) * s ^ (2 - nu))

/-- For p>1 and nu>2 the repaired coupled Lipschitz product tends to zero.
This is the quantitative reason the late-time backward map becomes a contraction. -/
theorem jointBackwardProduct_tendsto_zero
    (p nu CU L B : ℝ) (_hp : 1 < p) (hnu : 2 < nu) :
    Tendsto (jointBackwardProduct p nu CU L B) atTop (𝓝 0) := by
  have hpow : Tendsto (fun s : ℝ => s ^ (2 - nu)) atTop (𝓝 0) := by
    have he : -(nu - 2) = 2 - nu := by ring
    simpa only [he] using tendsto_rpow_neg_atTop (show 0 < nu - 2 by linarith)
  unfold jointBackwardProduct
  have h1 := hpow.const_mul ((CU * L) / (p + nu - 2))
  have h2 := h1.const_mul (B / (p - 1))
  simpa only [mul_zero, mul_assoc] using h2

/-- Joint product after adding the locally Lipschitz nonlinear centre source.
The first term is the propagated threshold feedback; the second is the
quadratic/higher Hartree remainder on a shrinking weighted ball. -/
def jointBackwardProductWithNonlinear
    (p nu delta CU L CN R B s : ℝ) : ℝ :=
  (B / (p - 1)) *
    ((CU * L) / (p + nu - 2) * s ^ (2 - nu) +
      CN * R * s ^ (-delta))

theorem jointBackwardProductWithNonlinear_tendsto_zero
    (p nu delta CU L CN R B : ℝ)
    (_hp : 1 < p) (hnu : 2 < nu) (hdelta : 0 < delta) :
    Tendsto (jointBackwardProductWithNonlinear
      p nu delta CU L CN R B) atTop (𝓝 0) := by
  have hfb : Tendsto
      (fun s : ℝ => (CU * L) / (p + nu - 2) * s ^ (2 - nu))
      atTop (𝓝 0) := by
    have he : -(nu - 2) = 2 - nu := by ring
    simpa only [he, mul_zero] using
      (tendsto_rpow_neg_atTop (show 0 < nu - 2 by linarith)).const_mul
        ((CU * L) / (p + nu - 2))
  have hnl : Tendsto (fun s : ℝ => CN * R * s ^ (-delta))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop hdelta).const_mul (CN * R)
  unfold jointBackwardProductWithNonlinear
  have hsum := hfb.add hnl
  have hprod := hsum.const_mul (B / (p - 1))
  simpa only [mul_zero, mul_assoc] using hprod

theorem eventually_jointBackwardProductWithNonlinear_lt_one
    (p nu delta CU L CN R B : ℝ)
    (hp : 1 < p) (hnu : 2 < nu) (hdelta : 0 < delta) :
    ∃ s0 : ℝ, ∀ s, s0 ≤ s →
      jointBackwardProductWithNonlinear p nu delta CU L CN R B s < 1 := by
  have h := jointBackwardProductWithNonlinear_tendsto_zero
    p nu delta CU L CN R B hp hnu hdelta
  have hm : Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds zero_lt_one
  have he := h.eventually hm
  rw [eventually_atTop] at he
  rcases he with ⟨s0, hs0⟩
  exact ⟨s0, fun s hs => hs0 s hs⟩

/-- Hence one can choose a terminal scale after which the product constant
is strictly below one. -/
theorem eventually_jointBackwardProduct_lt_one
    (p nu CU L B : ℝ) (hp : 1 < p) (hnu : 2 < nu) :
    ∃ s0 : ℝ, ∀ s, s0 ≤ s → jointBackwardProduct p nu CU L B s < 1 := by
  have h := jointBackwardProduct_tendsto_zero p nu CU L B hp hnu
  have hm : Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds zero_lt_one
  have he := h.eventually hm
  rw [eventually_atTop] at he
  rcases he with ⟨s0, hs0⟩
  exact ⟨s0, fun s hs => hs0 s hs⟩


theorem two_stage_backward_fixed_point
    {X Y : Type*}
    [MetricSpace X] [CompleteSpace X] [Nonempty X]
    [MetricSpace Y]
    (KA KQ : NNReal) (threshold : X → Y) (center : Y → X)
    (hA : LipschitzWith KA threshold)
    (hQ : LipschitzWith KQ center)
    (hsmall : KQ * KA < 1) :
    ∃! z : X × Y,
      z.2 = threshold z.1 ∧ z.1 = center z.2 := by
  let Phi : X → X := fun x => center (threshold x)
  have hLip : LipschitzWith (KQ * KA) Phi := by
    simpa only [Phi, Function.comp_def] using hQ.comp hA
  have hPhi : ContractingWith (KQ * KA) Phi := ⟨hsmall, hLip⟩
  let xstar : X := hPhi.fixedPoint Phi
  let ystar : Y := threshold xstar
  have hx : Phi xstar = xstar := hPhi.fixedPoint_isFixedPt
  refine ⟨(xstar, ystar), ?_, ?_⟩
  · exact ⟨rfl, hx.symm⟩
  · intro z hz
    rcases hz with ⟨hzA, hzQ⟩
    have hzfix : Phi z.1 = z.1 := by
      dsimp only [Phi]
      rw [← hzA, hzQ]
    have hzx : z.1 = xstar := by
      change z.1 = hPhi.fixedPoint Phi
      exact hPhi.fixedPoint_unique hzfix
    apply Prod.ext
    · exact hzx
    · rw [hzA, hzx]

#print axioms jointBackwardProduct_tendsto_zero
#print axioms jointBackwardProductWithNonlinear_tendsto_zero
#print axioms eventually_jointBackwardProductWithNonlinear_lt_one
#print axioms eventually_jointBackwardProduct_lt_one
#print axioms two_stage_backward_fixed_point

end HBL.MainBackward
