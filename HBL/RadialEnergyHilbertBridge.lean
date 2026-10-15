import HBL.RadialEnergyL2

/-!
Identification of the actual radial test with its Riesz functional on the
concrete Hilbert energy derivative coordinate.

For a smooth radial profile f, the expression
  integral_0^R zeta(r) * r * f(r) dr
equals the action of the bounded L2 Riesz functional with representer
  Q_zeta(s) = integral_s^R zeta(t) dt
on the L2 vector (r f(r))'.  The proof uses the previously verified
integration-by-parts identity and the almost-everywhere conversion from
classical functions into L2 vectors.

This closes the *finite-interval* functional-continuity bridge at the
level of actual, not abstract, radial tests.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation

/-- The test functional on smooth radial profiles is exactly the
Riesz pairing in the concrete L2 radial-energy coordinate. -/
theorem energyThresholdDual_on_radialCore
    (R : ℝ) (hR : 0 ≤ R)
    (zeta f : ℝ → ℝ)
    (hzeta : Continuous zeta) (hf : ContDiff ℝ 1 f) :
    energyThresholdDual R hR zeta hzeta
        (radialUDerivativeL2 R hR f hf) =
      (∫ r in (0 : ℝ)..R, zeta r * radialU f r) := by
  let mu : Measure ℝ := volume.restrict (Ioc (0 : ℝ) R)
  have hQ := testTailPrimitiveL2_ae R hR zeta hzeta
  have hg := radialUDerivativeL2_ae R hR f hf
  calc
    energyThresholdDual R hR zeta hzeta
        (radialUDerivativeL2 R hR f hf) =
        inner ℝ (testTailPrimitiveL2 R hR zeta hzeta)
          (radialUDerivativeL2 R hR f hf) := by
            exact energyThresholdDual_apply R hR zeta hzeta _
    _ = (∫ r, testTailPrimitive R zeta r * deriv (radialU f) r ∂mu) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hQ, hg] with r hrQ hrg
      rw [hrQ, hrg]
      simp [RCLike.inner_apply, mul_comm]
    _ = (∫ r in (0 : ℝ)..R, zeta r * radialU f r) := by
      rw [← intervalIntegral.integral_of_le hR]
      exact (compactTest_energy_coordinate_identity R zeta f hzeta hf).symm

end HBL.Modulation
