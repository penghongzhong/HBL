import HBL.TestedHamiltonCoupling.ActualIdentity
noncomputable section
namespace HBL.MainBackward
open HBL.Modulation
/-- Smooth radial profile whose radial conjugate is the fixed phase test. -/
def normalizedPhaseTestProfile (r : ℝ) : ℝ :=
  thresholdMinusMass⁻¹ * (thresholdBump r * bubble r)
end HBL.MainBackward
