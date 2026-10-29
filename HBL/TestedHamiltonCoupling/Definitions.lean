import HBL.RealThresholdCoupling
import HBL.ConstrainedCenterSpace

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
namespace HBL.MainBackward
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.TriangularRepair

/-- Actual tested Hamilton block: (Hminus imaginary, -Hplus real).
This is a bounded observation, not a bounded Hamilton generator. -/
def testedHamiltonCoupling
    (R : ℝ) (hR : 0 ≤ R) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 2 zeta)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hcut : ∀ r : ℝ, R ≤ r → g r = 0) : CenterPair →L[ℝ] (ℝ × ℝ) :=
  ((phaseThresholdCoupling R hR zeta hzeta).comp
    (ContinuousLinearMap.snd ℝ FullRadialEnergyL2 FullRadialEnergyL2)).prod
  (-((realThresholdCoupling g hg R hR hcut).comp
    (ContinuousLinearMap.fst ℝ FullRadialEnergyL2 FullRadialEnergyL2)))

/-- The same actual observation restricted to the closed constrained centre. -/
def constrainedTestedHamiltonCoupling
    (R : ℝ) (hR : 0 ≤ R) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 2 zeta)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hcut : ∀ r : ℝ, R ≤ r → g r = 0) :
    ConstrainedCenterSpace →L[ℝ] (ℝ × ℝ) :=
  (testedHamiltonCoupling R hR zeta hzeta g hg hcut).comp
    constrainedCenterSubmodule.subtypeL
end HBL.MainBackward
