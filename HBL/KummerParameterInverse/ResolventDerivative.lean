import HBL.KummerParameterInverse.BlockUnit
import Mathlib.Analysis.Calculus.FDeriv.Mul
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterResolvent_hasDerivAt {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (δ : ℂ)
    (hδ : ‖δ‖ * ‖T‖ ≤ (1 / 2 : ℝ)) :
    HasDerivAt (annulusParameterResolvent T)
      (-(annulusParameterResolvent T δ * annulusValueOperator T * annulusParameterResolvent T δ)) δ := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  let hu := annulusParameterBlock_isUnit T δ hδ
  have hi := hasFDerivAt_ringInverse (𝕜 := ℂ) (R := AnnulusSource z d →L[ℂ] AnnulusSource z d) hu.unit
  rw [hu.unit_spec, ← Ring.inverse_of_isUnit hu] at hi
  have hb : HasDerivAt (annulusParameterBlock T) (annulusValueOperator T) δ := by
    unfold annulusParameterBlock
    simpa only [one_smul, id_eq] using!
      ((hasDerivAt_id δ).smul_const (annulusValueOperator T)).const_add 1
  unfold annulusParameterResolvent
  simpa only [Function.comp_def, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, annulusParameterResolvent] using! hi.comp_hasDerivAt (F := AnnulusSource z d →L[ℂ] AnnulusSource z d)
      (E := AnnulusSource z d →L[ℂ] AnnulusSource z d) δ hb
end HBL.Profile.Kummer
