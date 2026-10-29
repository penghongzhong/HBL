import HBL.TypeIIDynamicSelection.ExteriorQuadraticSlowGain
import Mathlib.Tactic

/-!
# Physical Hartree slow-monopole gain at the actual moving cutoff

This is a concrete, non-axiomatic member of the "slow monopole" generated
source class used in manuscript prop:one-layer-stage3. It derives the
positive time order 2*beta-1 from the genuine radial Riesz exterior
potential, the manuscript radius R_c=4/|c|, the primitive decay of c(s)
and a separately stated physical exterior L1 mass estimate.

It does not assert the actual nonlinear radiation generates the stated
mass or that the full profile residual has been classified. Therefore
it is a proved physical component of prop:one-layer-stage3, not a proof
of the whole original manuscript environment.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- A concrete strict *positive* gain for the actual nonlocal slow-monopole
source. The original baseline weight is one, and the physical residual
component has order at least 2 beta. No output blowup rate is prescribed. -/
theorem actual_exteriorHartree_slow_monopole_gain
    (F : ℝ → ℝ) (hf : Measurable F)
    {c r s beta M : ℝ}
    (hF : IntegrableOn F (Ioi (monopoleQuadraticRadius c)))
    (hc : 0 < |c|) (hc1 : |c| ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : 1 ≤ s) (hbeta : (1 / 2 : ℝ) < beta)
    (hdec : |c| ≤ s ^ (-beta))
    (hMass : (∫ rho in Ioi (monopoleQuadraticRadius c), |F rho|) ≤ M) :
    0 < 2 * beta - 1 ∧
      |radialHartreeExteriorPotential F (monopoleQuadraticRadius c) r -
        radialHartreeExteriorCenter F (monopoleQuadraticRadius c)| ≤
          (Real.pi * hartreeKappa / 4 * M) * s ^ (-2 * beta) := by
  have hgain : 0 < 2 * beta - 1 := by linarith
  have hge := actual_exteriorHartree_gap_quadratic_fixed_core
    F hf hF hc hc1 hr hr1
  have hcoef : 0 ≤ Real.pi * hartreeKappa / 4 := by
    unfold hartreeKappa
    positivity
  have hcsq : c ^ 2 ≤ (s ^ (-beta)) ^ 2 := by
    calc
      c ^ 2 = |c| ^ 2 := (sq_abs c).symm
      _ ≤ (s ^ (-beta)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg c) hdec 2
  have hrsq : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
  have hMnonneg : 0 ≤ M := by
    exact le_trans (integral_nonneg (fun rho =>
      abs_nonneg (F rho))) hMass
  have hrpow : (s ^ (-beta)) ^ 2 = s ^ (-2 * beta) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ s) (-beta) 2]
    congr 1
    ring
  refine ⟨hgain, ?_⟩
  calc
    _ ≤ (Real.pi * hartreeKappa / 4 * c ^ 2 * r ^ 2) *
        ∫ rho in Ioi (monopoleQuadraticRadius c), |F rho| := hge
    _ ≤ (Real.pi * hartreeKappa / 4 * (s ^ (-beta)) ^ 2 * 1) * M := by
      gcongr
    _ = (Real.pi * hartreeKappa / 4 * M) * s ^ (-2 * beta) := by
      rw [hrpow]
      ring

end HBL.TypeIIDynamicSelection
