import HBL.KummerLocalInverse.PhysicalDefinitions
import HBL.KummerLocalInverse.ValueLinearity
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem physicalLocalKummer_linear
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d : ℝ)
    (hd : 0 ≤ d) (hde : d ≤ eps) (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G) (c : ℂ)
    {r : ℝ} (hr : r ∈ Icc (z - d) (z + d)) :
    physicalLocalKummerValue K d (fun s => F s + c * G s) r = physicalLocalKummerValue K d F r + c * physicalLocalKummerValue K d G r ∧
    physicalLocalKummerDeriv K d (fun s => F s + c * G s) r = physicalLocalKummerDeriv K d F r + c * physicalLocalKummerDeriv K d G r := by
  have ha : -d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
  have hb : d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
  have ht : r - z ∈ Icc (-eps) eps := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  exact localAnnulus_value_deriv_linear K (-d) d ha hb _ _
    (hF.comp (continuous_const.add continuous_id)) (hG.comp (continuous_const.add continuous_id)) c ht
end HBL.Profile.Kummer
