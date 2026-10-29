import HBL.RadialHartreeMultipole

/-!
# Explicit geometric separation gain for the actual exterior Hartree source

The already certified radial Riesz multipole estimate controls the inner
potential error by a weighted exterior mass. This module removes that
weighted-moment assumption altogether: an ordinary L1 exterior density
gives an explicit (r/R)^2 gain at radii 2r <= R.

For the full blowup proof a moving separation radius R(s) must be produced
by the actual three-region parametrix. No temporal rate is assumed here.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Spatial gain from the TRUE inverse-square Hartree exterior source:
the nonlocal center defect is O((r/R)^2) times the actual exterior L1 mass,
requiring no new weighted-moment hypothesis. -/
theorem actual_exteriorHartree_center_gap_L1_le
    (F : ℝ → ℝ) (hf : Measurable F)
    {R r : ℝ} (hF : IntegrableOn F (Ioi R))
    (hR : 0 < R) (hr : 0 < r) (hsep : 2 * r ≤ R) :
    |radialHartreeExteriorPotential F R r -
        radialHartreeExteriorCenter F R| ≤
    (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / R ^ 2)) *
      ∫ rho in Ioi R, |F rho| := by
  obtain ⟨hw, _, hpot⟩ :=
    radialHartreeExteriorPotential_quadratic_center F hf hF hR hr hsep
  have hi : IntegrableOn (fun rho => (1 / R ^ 2) * |F rho|) (Ioi R) :=
    hF.abs.const_mul (1 / R ^ 2)
  have hwide :
      (∫ rho in Ioi R, |F rho| / rho ^ 2) ≤
      (1 / R ^ 2) * (∫ rho in Ioi R, |F rho|) := by
    calc
      _ ≤ ∫ rho in Ioi R, (1 / R ^ 2) * |F rho| := by
        apply integral_mono_ae hw hi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
        have hsq : R ^ 2 ≤ rho ^ 2 :=
          pow_le_pow_left₀ hR.le hrho.le 2
        calc
          |F rho| / rho ^ 2 ≤ |F rho| / R ^ 2 :=
            div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hR) hsq
          _ = (1 / R ^ 2) * |F rho| := by ring
      _ = _ := by rw [integral_const_mul]
  have hcoeff : 0 ≤ 4 * Real.pi * hartreeKappa * r ^ 2 := by
    unfold hartreeKappa
    positivity
  calc
    _ ≤ (4 * Real.pi * hartreeKappa * r ^ 2) *
      (∫ rho in Ioi R, |F rho| / rho ^ 2) := hpot
    _ ≤ (4 * Real.pi * hartreeKappa * r ^ 2) *
      ((1 / R ^ 2) * (∫ rho in Ioi R, |F rho|)) :=
        mul_le_mul_of_nonneg_left hwide hcoeff
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
