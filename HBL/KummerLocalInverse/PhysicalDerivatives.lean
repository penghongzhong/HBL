import HBL.KummerLocalInverse.PhysicalDefinitions
import HBL.KummerLocalInverse.SecondDerivative
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem physicalLocalKummer_hasDerivAt
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d : ℝ)
    (hd : 0 < d) (hde : d < eps) (F : ℝ → ℂ) (hF : Continuous F)
    {r : ℝ} (hr : r ∈ Icc (z - d) (z + d)) :
    HasDerivAt (physicalLocalKummerValue K d F) (physicalLocalKummerDeriv K d F r) r ∧
    HasDerivAt (physicalLocalKummerDeriv K d F) (physicalLocalKummerSecond K d F r) r := by
  have ha : -d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
  have hb : d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
  have ht : r - z ∈ Ioo (-eps) eps := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hFs : Continuous (fun t => F (z + t)) := hF.comp (continuous_const.add continuous_id)
  have hsub : HasDerivAt (fun s : ℝ => s - z) 1 r := (hasDerivAt_id r).sub_const z
  have h1 := (localAnnulusValue_hasDerivAt K (-d) d ha hb _ hFs ht).scomp r hsub
  have h2 := (localAnnulusDeriv_hasDerivAt K (-d) d ha hb _ hFs ht).scomp r hsub
  unfold physicalLocalKummerValue physicalLocalKummerDeriv physicalLocalKummerSecond
  constructor
  · simpa only [one_smul, Function.comp_def] using h1
  · simpa only [one_smul, Function.comp_def] using h2
end HBL.Profile.Kummer
