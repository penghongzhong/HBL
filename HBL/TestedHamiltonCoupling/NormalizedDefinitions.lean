import HBL.TestedHamiltonCoupling.NormalizedProfiles
noncomputable section
namespace HBL.MainBackward
open HBL.Modulation
/-- Fixed scale/phase tested observation, in the manuscript coordinate order. -/
def normalizedHamiltonCoupling : CenterPair →L[ℝ] (ℝ × ℝ) :=
  testedHamiltonCoupling (Real.exp 1) (Real.exp_pos 1).le
    normalizedZetaPlus (normalizedZetaPlus_contDiff_infty.of_le (by simp))
    normalizedPhaseTestProfile normalizedHamiltonTest_profiles.1
    normalizedHamiltonTest_profiles.2.2.1

def normalizedConstrainedHamiltonCoupling :
    ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ) :=
  normalizedHamiltonCoupling.comp constrainedCenterSubmodule.subtypeL
end HBL.MainBackward
