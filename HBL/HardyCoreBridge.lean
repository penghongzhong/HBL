import HBL.BubbleScaleConnection
import HBL.ThresholdFunctionalBound

/-!
The first genuinely radial-energy norm bound for the compact tests.

The integration-by-parts Hardy lemma previously proved in
HBL.RadialHardy3D is linked here to the finite-interval L2 estimate
already used for the two orthogonality functionals.  The hypotheses
`f(R) = 0` and `C1` identify a compact radial core.  No global
claim for all of the completed homogeneous Sobolev space is made here:
the separate density/extension step is still pending.
-/

noncomputable section

open MeasureTheory Set

namespace HBL.Modulation

/-- Conversion of the finite radial Hardy inequality to restricted
Lebesgue-measure notation.  This gives the actual local L2 bound
from the weighted gradient energy, not an additional Hardy assumption. -/
theorem radialHardy3D_restrict
    (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hfR : f R = 0) :
    (∫ r, ‖f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc (0 : ℝ) R))) ≤
      4 * (∫ r in (0 : ℝ)..R, r ^ 2 * (deriv f r) ^ 2) := by
  have hrewrite :
      (∫ r, ‖f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc (0 : ℝ) R))) =
        ∫ r in (0 : ℝ)..R, (f r) ^ 2 := by
    rw [intervalIntegral.integral_of_le hR]
    congr 1
    funext r
    simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hrewrite]
  exact radialHardy3D R hR f hf hfR

/-- Exact local energy estimate for the original compact threshold test.
The right-hand side contains the radial gradient energy,
so the test is bounded on the compactly supported smooth radial core. -/
theorem compactThresholdPairing_energyCore_bound
    (R : ℝ) (hR : 0 ≤ R)
    (zeta f : ℝ → ℝ)
    (hzeta : Continuous zeta)
    (hf : ContDiff ℝ 1 f) (hfR : f R = 0) :
    |compactThresholdPairing R zeta f| ≤
      (∫ r, ‖zeta r‖ ^ (2 : ℝ) ∂
        (volume.restrict (Ioc (0 : ℝ) R))) ^ ((1 : ℝ) / 2) *
      (4 * R ^ 2 *
        (∫ r in (0 : ℝ)..R, r ^ 2 * (deriv f r) ^ 2)) ^
        ((1 : ℝ) / 2) := by
  exact compactThresholdPairing_abs_le_of_hardy
    R (∫ r in (0 : ℝ)..R, r ^ 2 * (deriv f r) ^ 2)
    hR zeta f hzeta hf.continuous
    (radialHardy3D_restrict R hR f hf hfR)

end HBL.Modulation
