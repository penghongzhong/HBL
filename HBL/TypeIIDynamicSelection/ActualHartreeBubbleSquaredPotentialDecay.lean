import HBL.TypeIIDynamicSelection.ActualHartreeBubbleSquaredRieszDecay
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# Revised HBL 2.13: original radial inverse-square Hartree Riesz potential
# of bubble^2 has genuine 1/(1+r) spatial decay

The original strictly audited positive radial logarithmic kernel gives
two estimates for the SAME absolutely convergent source row
 J(r)=int_0^infty rho*log((r+rho)/|r-rho|)*bubble(rho)^2 drho:
  J(r)/r <= radialHartreeBubbleBoundConstant  (preexisting strict lemma)
  J(r) <= 4+2|radialHartreeUnitLogMass|       (three-region new lemma).
Their sum controls (1+r)*J(r)/r without any additional region split:
  (1+r)*J(r)/r = J(r)/r+J(r).

Consequently the ORIGINAL radial 3D inverse-square Hartree potential
I[bubble^2](r) is <=C/(1+r) for all r>0.
No PV, exact arctan evaluation, assumed blowup rate, or extra axioms.
This is one scalar analytical bridge toward bounding the full mixed
Hartree nonlinear source and revising the one-layer finite profile.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.AffineTail HBL.Modulation.Monopole

/-- Explicit source-independent constant, assembled from actual
radial logarithmic kernel integrals already present in the paper. -/
def actualHartreeBubbleSquaredRieszDecayConstant : ℝ :=
  (2 * Real.pi * hartreeKappa) *
    (radialHartreeBubbleBoundConstant + 4 +
      2 * |radialHartreeUnitLogMass|)

theorem actualHartreeBubbleSquaredRieszDecayConstant_pos :
    0 < actualHartreeBubbleSquaredRieszDecayConstant := by
  unfold actualHartreeBubbleSquaredRieszDecayConstant
    hartreeKappa
  have hh := radialHartreeBubbleBoundConstant_pos
  positivity

/-- Exact original 3D inverse-square Riesz integral of the bubble-squared
density has positive inverse-radius decay, including both the origin
and far-field, without a manufactured local substitute. -/
theorem actual_Hartree_bubble_squared_Riesz_spatial_decay
    (r : ℝ) (hr : 0 < r) :
    radialHartreePotential (fun rho => bubble rho ^ 2) r ≤
      actualHartreeBubbleSquaredRieszDecayConstant / (1 + r) := by
  let J : ℝ := ∫ rho in Ioi (0 : ℝ),
    rho * hartreeRadialLog r rho * bubble rho ^ 2
  have hSmall : J ≤ r * radialHartreeBubbleBoundConstant := by
    simpa only [J] using (radialHartreeBubble_integrable_bound hr).2
  have hFar :
      J ≤ 4 + 2 * |radialHartreeUnitLogMass| := by
    simpa only [J] using actual_Hartree_bubble_squared_log_row_uniform hr
  have hDiv : J / r ≤ radialHartreeBubbleBoundConstant := by
    exact (div_le_iff₀ hr).2 (by
      simpa only [mul_comm] using hSmall)
  have hCoeff : 0 ≤ 2 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hProduct :
      (1 + r) * radialHartreePotential
          (fun rho => bubble rho ^ 2) r ≤
        actualHartreeBubbleSquaredRieszDecayConstant := by
    have hId :
        (1 + r) * radialHartreePotential
            (fun rho => bubble rho ^ 2) r =
          (2 * Real.pi * hartreeKappa) * (J / r + J) := by
      unfold radialHartreePotential
      dsimp only [J]
      field_simp [hr.ne']
      ring
    rw [hId]
    change (2 * Real.pi * hartreeKappa) * (J / r + J) ≤
      (2 * Real.pi * hartreeKappa) *
        (radialHartreeBubbleBoundConstant +
          (4 + 2 * |radialHartreeUnitLogMass|))
    apply mul_le_mul_of_nonneg_left _ hCoeff
    exact add_le_add hDiv hFar
  exact (le_div_iff₀ (by linarith : 0 < 1 + r)).2
    (by simpa only [mul_comm] using hProduct)

end HBL.TypeIIDynamicSelection
