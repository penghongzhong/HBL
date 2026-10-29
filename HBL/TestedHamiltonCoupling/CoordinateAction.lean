import HBL.TestedHamiltonCoupling.NormalizedIdentity
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
namespace HBL.MainBackward
open HBL.Modulation HBL.Modulation.AffineTail HBL.Modulation.Monopole

/-- Exact coordinate action on the smooth finite-energy Hamilton graph.
The graph equations are explicit domain conditions, not generator-existence assumptions. -/
theorem normalizedHamiltonCoupling_coordinate_action
    (f v a b : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hv : ContDiff ℝ 2 v)
    (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hfm : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hvm : MemLp (deriv (radialU v)) 2 halfLineMeasure)
    (ham : MemLp (deriv (radialU a)) 2 halfLineMeasure)
    (hbm : MemLp (deriv (radialU b)) 2 halfLineMeasure)
    (hA : ∀ r, radialU a r = hMinusApply (radialU v) r)
    (hB : ∀ r, radialU b r = -hPlusApply (radialU f) r) :
    normalizedHamiltonCoupling (smoothToRadialDotH1 f hfm, smoothToRadialDotH1 v hvm) =
      (scaleCompactTest (smoothToRadialDotH1 a ham),
       phaseCompactTest (smoothToRadialDotH1 b hbm)) := by
  rw [physicalScaleNormalization_certified.2.2.2.2.2.2.1 a ha ham,
    actualCompactPhaseSlice_certified.2.2.1 b hb hbm,
    (normalizedHamiltonCoupling_actual_identity f v hf hv hfm hvm).1]
  simp only [hA, hB, mul_neg, intervalIntegral.integral_neg]
end HBL.MainBackward
