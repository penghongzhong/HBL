import HBL.KummerSourceTangents.Definitions
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusSourceTangent_hasDerivAt {z d : ℝ}
    (S : ℝ → (AnnulusSource z d →L[ℂ] AnnulusJet z d))
    (F : ℝ → AnnulusSource z d) (t : ℝ) (q : ℂ) (G : AnnulusSource z d)
    (hS : HasDerivAt S (q • ((S t).comp (annulusValueOperator (S t)))) t)
    (hF : HasDerivAt F G t) :
    HasDerivAt (fun s => S s (F s)) (annulusSourceTangent (S t) q (F t) G) t := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  let R := ContinuousLinearMap.restrictScalarsL ℂ (AnnulusSource z d) (AnnulusJet z d) ℝ ℝ
  have hR := R.hasFDerivAt.comp_hasDerivAt
    (F := AnnulusSource z d →L[ℂ] AnnulusJet z d)
    (E := AnnulusSource z d →L[ℝ] AnnulusJet z d) t hS
  have h := hR.clm_apply hF
  convert h using 1
  · rfl
  · change S t (G + q • annulusValueProjection z d (S t (F t))) =
      q • S t (annulusValueProjection z d (S t (F t))) + S t G
    rw [map_add, map_smul]
    exact add_comm _ _
end HBL.Profile.Kummer
