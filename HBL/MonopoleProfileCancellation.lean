import HBL.MonopoleTailCharge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
The algebraic and time-integrability part of the manuscript's first slow
source cancellation lemma.  The Riesz-potential input is represented by an
arbitrary real linear map, so the expansion applies in particular to the
Hartree convolution operator without hiding any nonlinear Taylor input.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.Monopole

variable {α : Type*}

/-- Algebraic Hartree nonlinearity `kappa I(u^4) u^3`. -/
def hartreeNonlinearity
    (I : (α → ℝ) →ₗ[ℝ] (α → ℝ)) (kappa : ℝ)
    (u : α → ℝ) : α → ℝ :=
  fun x => kappa * I (fun y => u y ^ 4) x * u x ^ 3

/-- Its real first variation at `W` in the direction `X`. -/
def hartreeFirstVariation
    (I : (α → ℝ) →ₗ[ℝ] (α → ℝ)) (kappa : ℝ)
    (W X : α → ℝ) : α → ℝ :=
  fun x => kappa *
    (4 * I (fun y => W y ^ 3 * X y) x * W x ^ 3 +
      3 * I (fun y => W y ^ 4) x * W x ^ 2 * X x)

/-- The explicit polynomial left after removing the constant and linear
terms from `kappa I((W+cX)^4) (W+cX)^3`. -/
def hartreeQuadraticRemainder
    (I : (α → ℝ) →ₗ[ℝ] (α → ℝ)) (kappa : ℝ)
    (W X : α → ℝ) (c : ℝ) : α → ℝ :=
  fun x =>
    let A0 := I (fun y => W y ^ 4) x
    let A1 := 4 * I (fun y => W y ^ 3 * X y) x
    let A2 := 6 * I (fun y => W y ^ 2 * X y ^ 2) x
    let A3 := 4 * I (fun y => W y * X y ^ 3) x
    let A4 := I (fun y => X y ^ 4) x
    let B0 := W x ^ 3
    let B1 := 3 * W x ^ 2 * X x
    let B2 := 3 * W x * X x ^ 2
    let B3 := X x ^ 3
    kappa *
      ((A2 * B0 + A1 * B1 + A0 * B2) +
       c * (A3 * B0 + A2 * B1 + A1 * B2 + A0 * B3) +
       c ^ 2 * (A4 * B0 + A3 * B1 + A2 * B2 + A1 * B3) +
       c ^ 3 * (A4 * B1 + A3 * B2 + A2 * B3) +
       c ^ 4 * (A4 * B2 + A3 * B3) +
       c ^ 5 * (A4 * B3))

theorem linearMap_fourth_power_expansion
    (I : (α → ℝ) →ₗ[ℝ] (α → ℝ)) (W X : α → ℝ) (c : ℝ) (x : α) :
    I (fun y => (W y + c * X y) ^ 4) x =
      I (fun y => W y ^ 4) x +
      c * (4 * I (fun y => W y ^ 3 * X y) x) +
      c ^ 2 * (6 * I (fun y => W y ^ 2 * X y ^ 2) x) +
      c ^ 3 * (4 * I (fun y => W y * X y ^ 3) x) +
      c ^ 4 * I (fun y => X y ^ 4) x := by
  have hfun : (fun y => (W y + c * X y) ^ 4) =
      (fun y => W y ^ 4) +
      (4 * c) • (fun y => W y ^ 3 * X y) +
      (6 * c ^ 2) • (fun y => W y ^ 2 * X y ^ 2) +
      (4 * c ^ 3) • (fun y => W y * X y ^ 3) +
      c ^ 4 • (fun y => X y ^ 4) := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, map_add, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem hartree_nonlinearity_first_order_exact
    (I : (α → ℝ) →ₗ[ℝ] (α → ℝ)) (kappa c : ℝ)
    (W X : α → ℝ) (x : α) :
    hartreeNonlinearity I kappa (fun y => W y + c * X y) x =
      hartreeNonlinearity I kappa W x +
      c * hartreeFirstVariation I kappa W X x +
      c ^ 2 * hartreeQuadraticRemainder I kappa W X c x := by
  simp only [hartreeNonlinearity, hartreeFirstVariation,
    hartreeQuadraticRemainder]
  rw [linearMap_fourth_power_expansion I W X c x]
  ring

/-- The local cubic perturbation also has an explicit quadratic remainder
after its first source `c W^3` is removed. -/
def localCubicQuadraticRemainder
    (W X : α → ℝ) (c : ℝ) : α → ℝ :=
  fun x => 3 * W x ^ 2 * X x +
    3 * c * W x * X x ^ 2 + c ^ 2 * X x ^ 3

theorem local_cubic_first_order_exact
    (W X : α → ℝ) (c : ℝ) (x : α) :
    c * (W x + c * X x) ^ 3 =
      c * W x ^ 3 +
      c ^ 2 * localCubicQuadraticRemainder W X c x := by
  unfold localCubicQuadraticRemainder
  ring

/-- Static profile residual with an arbitrary linear Laplace part and the
actual algebraic Hartree nonlinearity. -/
def staticProfileResidual
    (A : (α → ℝ) →ₗ[ℝ] (α → ℝ))
    (I : (α → ℝ) →ₗ[ℝ] (α → ℝ)) (kappa c : ℝ)
    (W X : α → ℝ) : α → ℝ :=
  fun x =>
    A (fun y => W y + c * X y) x +
      hartreeNonlinearity I kappa (fun y => W y + c * X y) x +
      c * (W x + c * X x) ^ 3

/-- Exact cancellation of the complete order-`c` static source.  The two
hypotheses are precisely the bubble equation and `L_+ X = W^3`, written
without a sign convention hidden in notation. -/
theorem static_profile_linear_source_cancels
    (A : (α → ℝ) →ₗ[ℝ] (α → ℝ))
    (I : (α → ℝ) →ₗ[ℝ] (α → ℝ)) (kappa c : ℝ)
    (W X : α → ℝ)
    (hW : ∀ x, A W x + hartreeNonlinearity I kappa W x = 0)
    (hX : ∀ x, A X x + hartreeFirstVariation I kappa W X x = -W x ^ 3)
    (x : α) :
    staticProfileResidual A I kappa c W X x =
      c ^ 2 *
        (hartreeQuadraticRemainder I kappa W X c x +
          localCubicQuadraticRemainder W X c x) := by
  unfold staticProfileResidual
  have hAX : A (fun y => W y + c * X y) x =
      A W x + c * A X x := by
    have hfun : (fun y => W y + c * X y) = W + c • X := by
      funext y
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun, A.map_add, A.map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hAX]
  rw [hartree_nonlinearity_first_order_exact,
    local_cubic_first_order_exact]
  have hW' := hW x
  have hX' := hX x
  ring_nf at hW' hX' ⊢
  linear_combination hW' + c * hX'

/-- Standard domination lemma for polynomial time weights on a positive
half-line. -/
theorem integrableOn_of_abs_le_const_rpow
    (s0 a C : ℝ) (hs0 : 0 < s0) (ha : a < -1)
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f)
    (hbound : ∀ s, s0 < s → |f s| ≤ C * s ^ a) :
    IntegrableOn f (Ioi s0) := by
  have hpow : IntegrableOn (fun s : ℝ => s ^ a) (Ioi s0) :=
    integrableOn_Ioi_rpow_of_lt ha hs0
  have hmajor : IntegrableOn (fun s : ℝ => C * s ^ a) (Ioi s0) :=
    hpow.const_mul C
  refine hmajor.mono' hf.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact hbound s hs

/-- The four time orders in the manuscript are genuinely `L^1_s` whenever
`beta > 1/2` and `epsilon > 0`. -/
theorem monopole_time_orders_integrable
    (s0 beta epsilon : ℝ) (hs0 : 0 < s0)
    (hbeta : 1 / 2 < beta) (hepsilon : 0 < epsilon) :
    IntegrableOn (fun s : ℝ => s ^ (-2 * beta)) (Ioi s0) ∧
    IntegrableOn (fun s : ℝ => s ^ (-1 - beta)) (Ioi s0) ∧
    IntegrableOn (fun s : ℝ => s ^ (-1 - beta)) (Ioi s0) ∧
    IntegrableOn (fun s : ℝ => s ^ (-1 - epsilon)) (Ioi s0) := by
  have hsq : -2 * beta < -(1 : ℝ) := by linarith
  have hlin : -1 - beta < -(1 : ℝ) := by linarith
  have heps : -1 - epsilon < -(1 : ℝ) := by linarith
  exact ⟨integrableOn_Ioi_rpow_of_lt hsq hs0,
    integrableOn_Ioi_rpow_of_lt hlin hs0,
    integrableOn_Ioi_rpow_of_lt hlin hs0,
    integrableOn_Ioi_rpow_of_lt heps hs0⟩

end HBL.Modulation.Monopole
