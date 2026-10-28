import HBL.KummerLocalInverse.PhysicalDefinitions
import HBL.KummerLocalInverse.Equation
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem physicalLocalKummer_equation
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d : ℝ) (F : ℝ → ℂ) (r : ℝ) :
    physicalLocalKummerSecond K d F r + frozenFirstCoeff r * physicalLocalKummerDeriv K d F r +
      frozenZeroCoeff mu theta * physicalLocalKummerValue K d F r = F r := by
  have h := localAnnulus_equation K (-d) d (fun t => F (z + t)) (r - z)
  have he : z + (r - z) = r := by ring
  unfold physicalLocalKummerValue physicalLocalKummerDeriv physicalLocalKummerSecond
  simpa only [he] using h
end HBL.Profile.Kummer
