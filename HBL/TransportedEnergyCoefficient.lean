import HBL.TransportedTestTailL2Derivative

/-!
Correct energy-coordinate coefficient for the transported radial test.

The original compact threshold functional is
  integral zeta(r) * (r f(r)) dr.
After logarithmic scale transport and change of variables its coefficient
against the energy variable U f = r f is
  C_a(r) = exp(3a/2) * zeta(exp(a) r).

The earlier scalar kernel
  K_a(r) = exp(3a/2) * zeta(exp(a) r) * r
is the same functional when paired directly with f.  Thus K_a is useful
for scalar differentiation, but the Hilbert energy-coordinate tail must
be the primitive of C_a, not of K_a.  This module records the exact
conversion and the correct tail identity.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology

namespace HBL.Modulation

/-- Coefficient of the transported test against U f = r f. -/
def transportedEnergyCoefficient (zeta : ℝ → ℝ) (a r : ℝ) : ℝ :=
  Real.exp ((3 / 2 : ℝ) * a) * zeta (Real.exp a * r)

/-- Its logarithmic-scale derivative. -/
def transportedEnergyCoefficientDerivative
    (zeta : ℝ → ℝ) (a r : ℝ) : ℝ :=
  Real.exp ((3 / 2 : ℝ) * a) *
    ((3 / 2 : ℝ) * zeta (Real.exp a * r) +
      (Real.exp a * r) * deriv zeta (Real.exp a * r))

/-- The previously verified scalar test kernel is precisely the energy
coefficient multiplied by the radial factor. -/
theorem transportedRadialTest_eq_energyCoefficient_mul
    (zeta : ℝ → ℝ) (a r : ℝ) :
    transportedRadialTest zeta a r =
      transportedEnergyCoefficient zeta a r * r := by
  rfl

/-- Likewise for the logarithmic-scale derivative. -/
theorem transportedRadialTestDerivative_eq_energyCoefficientDerivative_mul
    (zeta : ℝ → ℝ) (a r : ℝ) :
    transportedRadialTestDerivative zeta a r =
      transportedEnergyCoefficientDerivative zeta a r * r := by
  rfl

@[simp]
theorem transportedEnergyCoefficient_zero
    (zeta : ℝ → ℝ) (r : ℝ) :
    transportedEnergyCoefficient zeta 0 r = zeta r := by
  simp [transportedEnergyCoefficient]

/-- Pointwise logarithmic-scale derivative of the correct energy coefficient. -/
theorem transportedEnergyCoefficient_hasDerivAt
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a r : ℝ) :
    HasDerivAt (fun b : ℝ => transportedEnergyCoefficient zeta b r)
      (transportedEnergyCoefficientDerivative zeta a r) a := by
  have hcoeff :
      HasDerivAt (fun b : ℝ => Real.exp ((3 / 2 : ℝ) * b))
        ((3 / 2 : ℝ) * Real.exp ((3 / 2 : ℝ) * a)) a := by
    have h := ((hasDerivAt_id a).mul_const (3 / 2 : ℝ)).exp
    simpa only [id_eq, one_mul, mul_comm] using h
  have harg :
      HasDerivAt (fun b : ℝ => Real.exp b * r)
        (Real.exp a * r) a := by
    simpa using (Real.hasDerivAt_exp a).mul_const r
  have hz :
      HasDerivAt (fun b : ℝ => zeta (Real.exp b * r))
        (deriv zeta (Real.exp a * r) * (Real.exp a * r)) a :=
    ((hzeta.differentiable (by norm_num)
      (Real.exp a * r)).hasDerivAt).comp a harg
  have hcalc := hcoeff.mul hz
  change HasDerivAt
    (fun b : ℝ => transportedEnergyCoefficient zeta b r) _ a at hcalc
  convert hcalc using 1
  dsimp [transportedEnergyCoefficientDerivative]
  ring

/-- Correct primitive representing the transported test in the
one-dimensional radial energy Hilbert coordinate. -/
def transportedEnergyTail
    (R : ℝ) (zeta : ℝ → ℝ) (a s : ℝ) : ℝ :=
  ∫ r in s..R, transportedEnergyCoefficient zeta a r

/-- At zero scale this is exactly the primitive of the original test. -/
theorem transportedEnergyTail_zero
    (R : ℝ) (zeta : ℝ → ℝ) (s : ℝ) :
    transportedEnergyTail R zeta 0 s =
      testTailPrimitive R zeta s := by
  apply intervalIntegral.integral_congr
  intro r _
  simp [transportedEnergyTail, testTailPrimitive]

/-- Pairing the correct transported energy tail with (U f)' gives exactly
the original transported scalar test integral. This is the decisive
factor-r consistency identity. -/
theorem transportedEnergyTail_pairing_eq_testIntegral
    (R : ℝ) (zeta f : ℝ → ℝ)
    (hzeta : ContDiff ℝ 1 zeta) (hf : ContDiff ℝ 1 f)
    (a : ℝ) :
    (∫ s in (0 : ℝ)..R,
      transportedEnergyTail R zeta a s * deriv (radialU f) s) =
      transportedRadialTestIntegral R zeta f a := by
  have hz : Continuous zeta := hzeta.continuous
  have hCoeff : Continuous (transportedEnergyCoefficient zeta a) := by
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * a) * zeta (Real.exp a * r))
    fun_prop
  have hId :=
    compactTest_energy_coordinate_identity
      R (transportedEnergyCoefficient zeta a) f hCoeff hf
  calc
    (∫ s in (0 : ℝ)..R,
      transportedEnergyTail R zeta a s * deriv (radialU f) s) =
      (∫ r in (0 : ℝ)..R,
        transportedEnergyCoefficient zeta a r * radialU f r) := by
          change (∫ s in (0 : ℝ)..R,
            testTailPrimitive R (transportedEnergyCoefficient zeta a) s *
              deriv (radialU f) s) =
            (∫ r in (0 : ℝ)..R,
              transportedEnergyCoefficient zeta a r * radialU f r)
          exact hId.symm
    _ = transportedRadialTestIntegral R zeta f a := by
      unfold transportedRadialTestIntegral
      apply intervalIntegral.integral_congr
      intro r _
      simp only [radialU, transportedRadialTest_eq_energyCoefficient_mul]
      ring

end HBL.Modulation
