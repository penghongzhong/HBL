import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import Mathlib.Tactic

/-!
# Dynamical derivative of the actual whole-radiation Hartree slow coefficient

The original manuscript coefficient is
  c_g(s) = kappa_H lambda(s)^(-1) m_0[z_g(t(s))],
not an externally prescribed exponent or the mass of an arbitrarily
fixed remote support. Write ell(s)=lambda(s)^(-1)>0.

The physical clock equations ell_s=-b ell, t_s=ell^2 and the actual
high-regularity radiation-moment differentiability give exactly
  c'_g=-b c_g + kappa_H ell^3 d_t m_0[z_g].
No terminal value or blowup exponent is used.

The radiation moment derivative and the physical clock conditions are
primitive regular-flow/modulation inputs here; proving their estimates
for the nonlinear selected Hartree orbit remains essential.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Exact full-radiation physical slow monopole coefficient at
renormalized time s, evaluated on the real rescaled radial source. -/
def actualPhysicalRadiationMonopole
    (ell : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ) (s : ℝ) : ℝ :=
  actualRadiationCenter (rescalePhysicalRadiation (ell s) (z (time s)))

/-- Derive the manuscript's complete slow-coefficient derivative from
the true rescaled whole-radiation center integral and the physical clock,
without imposing any rate or asymptotic modulation limit. -/
theorem actual_physical_radiation_slow_coefficient_hasDerivAt
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    {s dm : ℝ}
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hMoment : HasDerivAt
      (fun t => radialPhysicalQuarticMoment (z t)) dm (time s)) :
    HasDerivAt (actualPhysicalRadiationMonopole ell z time)
      (-(b s * actualPhysicalRadiationMonopole ell z time s) +
        hartreeKappa * (ell s) ^ 3 * dm) s := by
  let m : ℝ → ℝ := fun t => radialPhysicalQuarticMoment (z t)
  have hmt : HasDerivAt (fun t => m (time t)) (dm * (ell s) ^ 2) s :=
    hMoment.comp s hTime
  have hprod := (hEll.mul hmt).const_mul hartreeKappa
  have hvalue :
      actualPhysicalRadiationMonopole ell z time s =
        hartreeKappa * ell s * radialPhysicalQuarticMoment (z (time s)) := by
    exact actualRadiationCenter_equals_physical_slow_coefficient
      (ell s) hEllPos (z (time s))
  have hmodel : HasDerivAt
      (fun t => hartreeKappa *
        (ell t * radialPhysicalQuarticMoment (z (time t))))
      (-(b s * (hartreeKappa * ell s *
          radialPhysicalQuarticMoment (z (time s)))) +
        hartreeKappa * (ell s) ^ 3 * dm) s := by
    convert hprod using 1
    ring
  have hmodel' : HasDerivAt
      (fun t => hartreeKappa *
        (ell t * radialPhysicalQuarticMoment (z (time t))))
      (-(b s * actualPhysicalRadiationMonopole ell z time s) +
        hartreeKappa * (ell s) ^ 3 * dm) s := by
    rw [hvalue]
    exact hmodel
  have hne : ∀ᶠ t in 𝓝 s, 0 < ell t :=
    hEll.continuousAt.tendsto.eventually (Ioi_mem_nhds hEllPos)
  have heq :
      (actualPhysicalRadiationMonopole ell z time) =ᶠ[𝓝 s]
        (fun t => hartreeKappa * (ell t *
          radialPhysicalQuarticMoment (z (time t)))) := by
    filter_upwards [hne] with t ht
    simpa only [mul_assoc] using
      (actualRadiationCenter_equals_physical_slow_coefficient
        (ell t) ht (z (time t)))
  exact hmodel'.congr_of_eventuallyEq heq

end HBL.TypeIIDynamicSelection
