import HBL.RadialTestEnergyBound
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
Concrete real Hilbert realization of the radial energy derivative coordinate.

The half-line coordinate q=(r f)' is in L2(dr). On a finite cutoff Ioc 0 R
the primitive of each compact threshold test is also in L2. We use the
Riesz pairing to produce a genuine continuous linear functional on this
concrete Hilbert space, with its precise operator bound.

This file constructs the finite-cutoff Hilbert representation and verifies
its analytic properties. It does NOT yet assert equivalence with all of
the infinite-radius radial homogeneous Sobolev space.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation

/-- Finite-radius real Hilbert space for the radial energy derivative. -/
abbrev RadialEnergyL2 (R : ℝ) : Type :=
  Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) R))

/-- The primitive of a compact smooth test is a concrete vector in L2. -/
def testTailPrimitiveL2 (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : Continuous zeta) :
    RadialEnergyL2 R :=
  (continuous_memLp_restrict_Ioc 0 R hR
    (testTailPrimitive R zeta)
    (testTailPrimitive_contDiff_one R zeta hzeta).continuous 2).toLp
      (testTailPrimitive R zeta)

/-- The primitive L2 vector represents its original scalar function almost
everywhere on the compact radial interval. -/
theorem testTailPrimitiveL2_ae (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : Continuous zeta) :
    (testTailPrimitiveL2 R hR zeta hzeta : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) R)] testTailPrimitive R zeta := by
  exact (continuous_memLp_restrict_Ioc 0 R hR
    (testTailPrimitive R zeta)
    (testTailPrimitive_contDiff_one R zeta hzeta).continuous 2).coeFn_toLp

/-- Derivative of U(f)=r f(r), regarded as a vector in the finite-radius
real energy Hilbert space. -/
def radialUDerivativeL2 (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    RadialEnergyL2 R :=
  (continuous_memLp_restrict_Ioc 0 R hR
    (deriv (radialU f))
    (radialU_contDiff_one f hf).continuous_deriv_one 2).toLp
      (deriv (radialU f))

/-- The radial derivative Hilbert vector agrees almost everywhere with
the original classical radial derivative. -/
theorem radialUDerivativeL2_ae
    (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    (radialUDerivativeL2 R hR f hf : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) R)] deriv (radialU f) := by
  exact (continuous_memLp_restrict_Ioc 0 R hR
    (deriv (radialU f))
    (radialU_contDiff_one f hf).continuous_deriv_one 2).coeFn_toLp

/-- Concrete continuous threshold functional on the radial energy Hilbert
coordinate, given by the Riesz pairing with the primitive of the test. -/
def energyThresholdDual (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : Continuous zeta) :
    RadialEnergyL2 R →L[ℝ] ℝ :=
  innerSL ℝ (testTailPrimitiveL2 R hR zeta hzeta)

/-- The operator action is the real Hilbert inner product. -/
theorem energyThresholdDual_apply
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : Continuous zeta)
    (q : RadialEnergyL2 R) :
    energyThresholdDual R hR zeta hzeta q =
      inner ℝ (testTailPrimitiveL2 R hR zeta hzeta) q := by
  rfl

/-- Sharp operator bound of the actual threshold functional. -/
theorem energyThresholdDual_bound
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : Continuous zeta)
    (q : RadialEnergyL2 R) :
    ‖energyThresholdDual R hR zeta hzeta q‖ ≤
      ‖testTailPrimitiveL2 R hR zeta hzeta‖ * ‖q‖ := by
  rw [energyThresholdDual_apply]
  exact norm_inner_le_norm _ _

end HBL.Modulation
