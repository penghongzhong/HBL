import HBL.RadialHartreeMultipole
import HBL.MonopoleComplexResidual
import HBL.MonopoleOuterCubic

/-!
The physical exterior Hartree potential supplies the slow cubic term.

This is a genuine inverse-square *radial Hartree* calculation, using the
actual exterior Riesz potential, not a local nonlinear surrogate. The
radial exterior density is measurable and L1 on (R,infinity). Its exact
center mass is an integral; no prescribed speed or terminal coefficient
is introduced.

This establishes the local physical potential-to-effective-residual
matching on 2r<=R. It does NOT identify exterior F with the density of an
already constructed global PDE orbit, nor close the three-region parametrix.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole

/-- The original radial Hartree residual including a *genuine* exterior
Riesz-potential contribution in the inner region. The extra term is
the exterior nonlocal source, not a newly postulated local PDE term. -/
def monopoleExteriorHartreeIncrement
    (F : ℝ → ℝ) (R : ℝ)
    (c b omega : ℝ → ℝ) (s r : ℝ) : ℂ :=
  complexRadialRenormalizedResidual
    (fun t x => (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c t)) (c t) x : ℂ)) (b s) (omega s) s r +
  (radialHartreeExteriorPotential F R r : ℂ) *
    (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c s)) (c s) r : ℂ) ^ 3 -
  complexRadialRenormalizedResidual
    (fun _ x => (bubble x : ℂ)) (b s) (omega s) s r

/-- EXACT difference between the former *effective* local cubic and the
genuine exterior Hartree convolution: a coefficient error times V_c^3. -/
theorem monopoleEffective_minus_actualExterior_exact
    (F : ℝ → ℝ) (R : ℝ) (c b omega : ℝ → ℝ) (s r : ℝ) :
    monopoleComplexEffectiveIncrement c (b s) (omega s) s r -
      monopoleExteriorHartreeIncrement F R c b omega s r =
    ((c s - radialHartreeExteriorPotential F R r : ℝ) : ℂ) *
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c s)) (c s) r : ℂ) ^ 3 := by
  unfold monopoleComplexEffectiveIncrement
    monopoleExteriorHartreeIncrement
  push_cast
  ring

/-- If the slow amplitude equals the actual exterior density's center
mass, the local cubic discrepancy is O(r^2), quantitatively, directly
from the already proved exact exterior radial Hartree multipole bound. -/
theorem monopoleEffective_actualExterior_match_norm_le
    (F : ℝ → ℝ) (hFmeas : Measurable F)
    {R r c : ℝ}
    (hF : IntegrableOn F (Ioi R))
    (hR : 0 < R) (hr : 0 < r) (hsep : 2 * r ≤ R)
    (hc : |c| ≤ 1)
    (hcenter : c = radialHartreeExteriorCenter F R) :
    ‖((c - radialHartreeExteriorPotential F R r : ℝ) : ℂ) *
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c r : ℂ) ^ 3‖ ≤
    (4 * Real.pi * hartreeKappa * r ^ 2 *
      ∫ rho in Ioi R, |F rho| / rho ^ 2) *
      (1 + monopoleRadialBoundConstant) ^ 3 := by
  have hpot := (radialHartreeExteriorPotential_quadratic_center
    F hFmeas hF hR hr hsep).2.2
  have herr : |c - radialHartreeExteriorPotential F R r| ≤
    4 * Real.pi * hartreeKappa * r ^ 2 *
      ∫ rho in Ioi R, |F rho| / rho ^ 2 := by
    rw [hcenter, abs_sub_comm]
    exact hpot
  have hv := monopolePerturbedRadialProfile_abs_le hr hc
  have hpow : |monopolePerturbedRadialProfile
      (monopoleQuadraticRadius c) c r| ^ 3 ≤
      (1 + monopoleRadialBoundConstant) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hv 3
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul herr hpow (by positivity)
    ((abs_nonneg _).trans herr)

/-- The physical Hartree exterior potential is a certified source of the
exact local cubic compensation, with a quadratic spatial error. This is
a matched-source estimate, not an independently constructed PDE orbit. -/
theorem monopoleEffective_actualExterior_residual_diff_norm_le
    (F : ℝ → ℝ) (hFmeas : Measurable F)
    {R r : ℝ} (c b omega : ℝ → ℝ) (s : ℝ)
    (hF : IntegrableOn F (Ioi R))
    (hR : 0 < R) (hr : 0 < r) (hsep : 2 * r ≤ R)
    (hc : |c s| ≤ 1)
    (hcenter : c s = radialHartreeExteriorCenter F R) :
    ‖monopoleComplexEffectiveIncrement c (b s) (omega s) s r -
      monopoleExteriorHartreeIncrement F R c b omega s r‖ ≤
    (4 * Real.pi * hartreeKappa * r ^ 2 *
      ∫ rho in Ioi R, |F rho| / rho ^ 2) *
      (1 + monopoleRadialBoundConstant) ^ 3 := by
  rw [monopoleEffective_minus_actualExterior_exact]
  exact monopoleEffective_actualExterior_match_norm_le
    F hFmeas hF hR hr hsep hc hcenter

end HBL.TypeIIDynamicSelection
