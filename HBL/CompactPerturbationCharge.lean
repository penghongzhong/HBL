import HBL.WeightedHartreePointwiseBound

/-!
Actual Hartree pairing on the weighted L2 domain.  These lemmas supply the
nonlocal part of a compact-perturbation charge argument.  They do not yet
assert the local integration-by-parts identity for arbitrary perturbations.
-/

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

theorem weightedPerturbation_hartree_pairing_ae
    (p q : ℝ → ℝ)
    (hp : MemLp (fun r => weightedGreenDecay r * p r) 2 halfLineMeasure)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure) :
    (fun r => hp.toLp (fun s => weightedGreenDecay s * p s) r *
      weightedHartreeOperator
        (hq.toLp (fun s => weightedGreenDecay s * q s)) r) =ᵐ[halfLineMeasure]
      (fun r => p r * nonlocalApply q r) := by
  filter_upwards [hp.coeFn_toLp,
    weightedHartreeOperator_ae_pointwise
      (hq.toLp (fun s => weightedGreenDecay s * q s))] with r hpR hTR
  rw [hpR, hTR, weightedHartreePointwise_conjugation q hq]
  unfold weightedGreenDecay
  field_simp

theorem hartree_pairing_integrable_of_weighted_memLp
    (p q : ℝ → ℝ)
    (hp : MemLp (fun r => weightedGreenDecay r * p r) 2 halfLineMeasure)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure) :
    Integrable (fun r => p r * nonlocalApply q r) halfLineMeasure := by
  exact ((Lp.memLp (hp.toLp (fun r => weightedGreenDecay r * p r))).integrable_mul
    (Lp.memLp (weightedHartreeOperator
      (hq.toLp (fun r => weightedGreenDecay r * q r))))).congr
    (weightedPerturbation_hartree_pairing_ae p q hp hq)

theorem hartree_pairing_eq_of_weighted_memLp
    (p q : ℝ → ℝ)
    (hp : MemLp (fun r => weightedGreenDecay r * p r) 2 halfLineMeasure)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure) :
    (∫ r in Ioi (0 : ℝ), p r * nonlocalApply q r) =
      ∫ r in Ioi (0 : ℝ), q r * nonlocalApply p r := by
  let x := hp.toLp (fun r => weightedGreenDecay r * p r)
  let y := hq.toLp (fun r => weightedGreenDecay r * q r)
  have hi (p q : ℝ → ℝ)
      (hp : MemLp (fun r => weightedGreenDecay r * p r) 2 halfLineMeasure)
      (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure) :
      inner ℝ (hp.toLp (fun r => weightedGreenDecay r * p r))
        (weightedHartreeOperator (hq.toLp (fun r => weightedGreenDecay r * q r))) =
      ∫ r in Ioi (0 : ℝ), p r * nonlocalApply q r := by
    rw [L2.inner_def]
    change (∫ r, inner ℝ _ _ ∂halfLineMeasure) = _
    simp only [Real.inner_apply]
    exact integral_congr_ae (weightedPerturbation_hartree_pairing_ae p q hp hq)
  rw [← hi p q hp hq, ← hi q p hq hp]
  change inner ℝ x (weightedHartreeOperator y) = inner ℝ y (weightedHartreeOperator x)
  calc
    inner ℝ x (weightedHartreeOperator y) = inner ℝ (weightedHartreeOperator x) y :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        weightedHartreeOperator_selfAdjoint x y).symm
    _ = inner ℝ y (weightedHartreeOperator x) := real_inner_comm _ _

end HBL.Modulation.Monopole
