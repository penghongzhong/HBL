import HBL.WeightedPhaseAffineSource
import HBL.AffineTailPlusGreen
import Mathlib.Tactic

/-!
# Real-channel local affine source in the manuscript weighted L2 class

The actual H-plus local affine source is
  H_plus^local(model) = 3 H_minus(model) + 2 model'',
where model = chi_aff*r.  The first term is already known to be in
L^(2,sigma), sigma<=2; the second is compactly supported on the positive
half-line and hence belongs to every such weighted L2 space.

No far-field or nonlocal Hartree bound is assumed.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff

namespace HBL.Modulation.AffineTail

def affineModelSecondDerivative (r : ℝ) : ℝ :=
  deriv (deriv model) r

theorem affineModelSecondDerivative_continuous :
    Continuous affineModelSecondDerivative := by
  have hq : ContDiff ℝ ∞ model := model_contDiff_infty
  have hq1 : ContDiff ℝ ∞ (deriv model) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hq2 : ContDiff ℝ ∞ (deriv (deriv model)) :=
    (contDiff_infty_iff_deriv.mp hq1).2
  exact hq2.continuous

theorem affineModelSecondDerivative_far (r : ℝ) (hr : 2 < r) :
    affineModelSecondDerivative r = 0 :=
  model_second_deriv_eq_zero_of_two_lt r hr

theorem affineModelSecondDerivative_inWeightedL2
    (sigma : ℝ) :
    InWeightedL2 sigma affineModelSecondDerivative := by
  have hc : Continuous (fun r : ℝ =>
      affineJapaneseWeight sigma r * affineModelSecondDerivative r) :=
    (affineJapaneseWeight_continuous sigma).mul
      affineModelSecondDerivative_continuous
  have hcompact : IntegrableOn (fun r : ℝ =>
      (affineJapaneseWeight sigma r *
        affineModelSecondDerivative r) ^ 2) (Ioc (0 : ℝ) 2) :=
    (hc.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have htail : IntegrableOn (fun r : ℝ =>
      (affineJapaneseWeight sigma r *
        affineModelSecondDerivative r) ^ 2) (Ioi 2) := by
    refine integrableOn_zero.congr_fun ?_ measurableSet_Ioi
    intro r hr
    simp [affineModelSecondDerivative_far r hr]
  have hall : IntegrableOn (fun r : ℝ =>
      (affineJapaneseWeight sigma r *
        affineModelSecondDerivative r) ^ 2) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 by norm_num)]
    exact hcompact.union htail
  unfold InWeightedL2
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable.restrict).2
  exact hall

theorem hPlusLocalAffineSource_identity (r : ℝ) :
    hPlusLocalApply model r =
      3 * channelAffineSource HartreeChannel.minus r +
        2 * affineModelSecondDerivative r := by
  change
    -deriv (deriv model) r - 3 * potential r * model r =
      3 * (-deriv (deriv model) r - potential r * model r) +
        2 * deriv (deriv model) r
  ring

theorem hPlusLocalAffineSource_inWeightedL2
    (sigma : ℝ) (hsigma : sigma ≤ 2) :
    InWeightedL2 sigma (hPlusLocalApply model) := by
  have hphase := phaseAffineSource_inWeightedL2 sigma hsigma
  have hdd := affineModelSecondDerivative_inWeightedL2 sigma
  unfold InWeightedL2 at hphase hdd ⊢
  have h := (hphase.const_mul (3 : ℝ)).add (hdd.const_mul (2 : ℝ))
  convert h using 1
  funext r
  simp only [Pi.add_apply, Pi.mul_apply]
  rw [hPlusLocalAffineSource_identity]
  ring

#print axioms affineModelSecondDerivative_inWeightedL2
#print axioms hPlusLocalAffineSource_identity
#print axioms hPlusLocalAffineSource_inWeightedL2

end HBL.Modulation.AffineTail
