import HBL.TypeIIDynamicSelection.ExteriorSpatialGain
import HBL.MonopoleQuadraticCutoff

/-!
# The actual manuscript cutoff converts spatial gain into quadratic slow gain

The genuine monopole truncation uses R_c = 4 / |c|. The already verified
exterior Hartree (r/R)^2 source estimate consequently has coefficient
(pi*kappa_H/4) c^2 r^2. This is an explicit nonlocal mechanism for the
temporal L1 threshold 2*beta>1 once c(s)=O(s^{-beta}) is *proved* from
physical modulation.

The result assumes c != 0 to avoid totalized division at zero.
Crossing-zero amplitude paths and the scalar mass matching c=C_F remain
separate physical construction tasks; no blowup rate is postulated.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- A true geometric identity for the manuscript's moving monopole cutoff.
No numerical speed exponent is used. -/
theorem actual_monopole_radius_inverse_square
    {c : ℝ} (_hc : 0 < |c|) :
    1 / (monopoleQuadraticRadius c) ^ 2 = c ^ 2 / 16 := by
  unfold monopoleQuadraticRadius
  have hsq : |c| ^ 2 = c ^ 2 := sq_abs c
  field_simp [_hc.ne']
  nlinarith [hsq]

/-- Actual exterior inverse-square Hartree coefficient gains c^2 at the
same quadratic-radius cutoff used by the physical monopole profile. -/
theorem actual_exteriorHartree_gap_quadratic_in_c
    (F : ℝ → ℝ) (hf : Measurable F) {c r : ℝ}
    (hF : IntegrableOn F (Ioi (monopoleQuadraticRadius c)))
    (hc : 0 < |c|) (hr : 0 < r)
    (hsep : 2 * r ≤ monopoleQuadraticRadius c) :
    |radialHartreeExteriorPotential F (monopoleQuadraticRadius c) r -
       radialHartreeExteriorCenter F (monopoleQuadraticRadius c)| ≤
     (Real.pi * hartreeKappa / 4 * c ^ 2 * r ^ 2) *
       ∫ rho in Ioi (monopoleQuadraticRadius c), |F rho| := by
  have hR : 0 < monopoleQuadraticRadius c := by
    unfold monopoleQuadraticRadius
    exact div_pos (by norm_num) hc
  have he := actual_exteriorHartree_center_gap_L1_le F hf hF
    hR hr hsep
  calc
    _ ≤ (4 * Real.pi * hartreeKappa * r ^ 2 *
        (1 / (monopoleQuadraticRadius c) ^ 2)) *
          ∫ rho in Ioi (monopoleQuadraticRadius c), |F rho| := he
    _ = _ := by
      rw [actual_monopole_radius_inverse_square hc]
      ring

/-- The estimate holds throughout the fixed normalized physical core
0<r<=1 when |c|<=1: no arbitrary extra annulus is imposed. -/
theorem actual_exteriorHartree_gap_quadratic_fixed_core
    (F : ℝ → ℝ) (hf : Measurable F) {c r : ℝ}
    (hF : IntegrableOn F (Ioi (monopoleQuadraticRadius c)))
    (hc : 0 < |c|) (hc1 : |c| ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    |radialHartreeExteriorPotential F (monopoleQuadraticRadius c) r -
       radialHartreeExteriorCenter F (monopoleQuadraticRadius c)| ≤
     (Real.pi * hartreeKappa / 4 * c ^ 2 * r ^ 2) *
       ∫ rho in Ioi (monopoleQuadraticRadius c), |F rho| := by
  have hR := monopoleQuadraticRadius_ge_four hc hc1
  apply actual_exteriorHartree_gap_quadratic_in_c F hf hF hc hr
  linarith

end HBL.TypeIIDynamicSelection
