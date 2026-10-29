import HBL.KummerSourceTangents.Definitions
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusJet_parameter_derivative_pointwise {z d : ℝ}
    (U : ℝ → AnnulusJet z d) (V : AnnulusJet z d) (t : ℝ)
    (hU : HasDerivAt U V t) (r : PhysicalAnnulus z d) :
    HasDerivAt (fun s => (U s r).1) (V r).1 t ∧
    HasDerivAt (fun s => (U s r).2) (V r).2 t := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have he := (ContinuousMap.evalCLM (R := ℝ) r).hasFDerivAt.comp_hasDerivAt
    (F := AnnulusJet z d) (E := ℂ × ℂ) t hU
  exact ⟨he.fst,he.snd⟩
end HBL.Profile.Kummer
