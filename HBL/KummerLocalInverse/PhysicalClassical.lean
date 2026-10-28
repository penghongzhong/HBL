import HBL.KummerLocalInverse.PhysicalDerivatives
import HBL.KummerLocalInverse.PhysicalEquation
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem physicalLocalKummer_classical
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d : ℝ)
    (hd : 0 < d) (hde : d < eps) (F : ℝ → ℂ) (hF : Continuous F)
    {r : ℝ} (hr : r ∈ Icc (z - d) (z + d)) :
    HasDerivAt (deriv (physicalLocalKummerValue K d F)) (physicalLocalKummerSecond K d F r) r ∧
    deriv (deriv (physicalLocalKummerValue K d F)) r +
      frozenFirstCoeff r * deriv (physicalLocalKummerValue K d F) r +
      frozenZeroCoeff mu theta * physicalLocalKummerValue K d F r = F r := by
  have hD := physicalLocalKummer_hasDerivAt K d hd hde F hF hr
  have hDD : HasDerivAt (deriv (physicalLocalKummerValue K d F)) (physicalLocalKummerSecond K d F r) r := by
    apply hD.2.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (show z - eps < r by linarith [hr.1])
      (show r < z + eps by linarith [hr.2])] with s hs
    have ha : -d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
    have hb : d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
    have ht : s - z ∈ Ioo (-eps) eps := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hFs : Continuous (fun t => F (z + t)) := hF.comp (continuous_const.add continuous_id)
    have h := (localAnnulusValue_hasDerivAt K (-d) d ha hb _ hFs ht).scomp s ((hasDerivAt_id s).sub_const z)
    have hval : HasDerivAt (physicalLocalKummerValue K d F) (physicalLocalKummerDeriv K d F s) s := by
      unfold physicalLocalKummerValue physicalLocalKummerDeriv
      simpa only [one_smul, Function.comp_def, id_eq] using h
    exact hval.deriv
  refine ⟨hDD, ?_⟩
  rw [hDD.deriv, hD.1.deriv]
  exact physicalLocalKummer_equation K d F r
end HBL.Profile.Kummer
