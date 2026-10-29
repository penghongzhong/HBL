import HBL.TestedHamiltonCoupling.CoordinateAction
import HBL.HamiltonCoreGraph.EnergyProfileInjective
import HBL.HamiltonCoreGraph.CoordinateCongruence
import HBL.HamiltonCoreGraph.OperatorCongruence
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace HBL.MainBackward
open HBL.Modulation HBL.Modulation.AffineTail
/-- Actual smooth finite-energy Hamilton graph, with equations imposed only
on the positive half-line. Closedness, density and generation are separate obligations. -/
def SmoothHamiltonGraph (q y : CenterPair) : Prop :=
  ∃ f v a b : ℝ → ℝ, ∃ _hf : ContDiff ℝ 2 f, ∃ _hv : ContDiff ℝ 2 v,
  ∃ _ha : ContDiff ℝ 1 a, ∃ _hb : ContDiff ℝ 1 b,
  ∃ hfm : MemLp (deriv (radialU f)) 2 halfLineMeasure,
  ∃ hvm : MemLp (deriv (radialU v)) 2 halfLineMeasure,
  ∃ ham : MemLp (deriv (radialU a)) 2 halfLineMeasure,
  ∃ hbm : MemLp (deriv (radialU b)) 2 halfLineMeasure,
  q = (smoothToRadialDotH1 f hfm, smoothToRadialDotH1 v hvm) ∧
  y = (smoothToRadialDotH1 a ham, smoothToRadialDotH1 b hbm) ∧
  (∀ r, 0 < r → radialU a r = hMinusApply (radialU v) r) ∧
  (∀ r, 0 < r → radialU b r = -hPlusApply (radialU f) r)
end HBL.MainBackward
