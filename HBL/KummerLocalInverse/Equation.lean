import HBL.KummerLocalInverse.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localAnnulus_equation
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (a b : ℝ) (F : ℝ → ℂ) (t : ℝ) :
    localAnnulusSecond K a b F t + frozenFirstCoeff (z + t) * localAnnulusDeriv K a b F t +
      frozenZeroCoeff mu theta * localAnnulusValue K a b F t = F t := by
  unfold localAnnulusSecond localAnnulusValue localAnnulusDeriv
  ring
end HBL.Profile.Kummer
