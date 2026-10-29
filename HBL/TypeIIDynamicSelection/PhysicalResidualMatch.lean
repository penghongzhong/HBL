import HBL.TypeIIDynamicSelection.RemoteComplexInteraction
import HBL.TypeIIDynamicSelection.ExteriorHartreeMatch

/-!
# Exact inner Hartree residual versus remote-radiation potential

This module uses the SAME physical radial nonlocal Hartree residual as the
manuscript. On the inner region 2r<=R, complex remote radiation supported
outside R does not change any local temporal or radial differential term.
Its only effect is the real exterior Riesz quartic-density potential times
the original real inner cubic. This is an exact, not assumed, identity.

Matching the slow monopole amplitude c(s) with the remote density's
physical center moment is a separate (unproved) solvability condition;
when that condition holds, the discrepancy is O(r²) with explicit
weighted exterior mass. Neither PDE orbit existence nor time-weight
smallness is inferred from the spatial estimate.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation HBL.Modulation.AffineTail

/-- The inner profile used in the actual radial Hartree monopole
correction, not a generic abstract profile. -/
def monopoleInnerComplexProfile (c : ℝ → ℝ) (s r : ℝ) : ℂ :=
  (monopolePerturbedRadialProfile
    (monopoleQuadraticRadius (c s)) (c s) r : ℂ)

/-- Append complex remote radiation without adding any local cubic term
to the Hartree equation. -/
def monopoleWithRemoteRadiation (c : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (s r : ℝ) : ℂ :=
  monopoleInnerComplexProfile c s r + Z s r

/-- Since Z vanishes throughout the physical core at every time,
the FULL renormalized Hartree residual difference equals just the
genuine Hartree nonlinear source difference. The time derivative, radial
Laplacian and dilation all cancel exactly, without derivative assumptions. -/
theorem actual_full_radial_residual_remote_eq_nonlin
    (c b omega : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {R s r : ℝ} (hr : 0 < r) (hsep : 2 * r ≤ R)
    (hZ : ∀ t rho, rho ≤ R → Z t rho = 0) :
    complexRadialRenormalizedResidual
      (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
      complexRadialRenormalizedResidual
        (monopoleInnerComplexProfile c) (b s) (omega s) s r =
    complexRadialHartreeNonlinearity
      (monopoleWithRemoteRadiation c Z s) r -
      complexRadialHartreeNonlinearity (monopoleInnerComplexProfile c s) r := by
  have hrR : r < R := by linarith
  have hrle : r ≤ R := hrR.le
  have htfn : (fun t => monopoleWithRemoteRadiation c Z t r) =
      (fun t => monopoleInnerComplexProfile c t r) := by
    funext t
    simp only [monopoleWithRemoteRadiation, hZ t r hrle, add_zero]
  have ht :
      deriv (fun t => monopoleWithRemoteRadiation c Z t r) s =
        deriv (fun t => monopoleInnerComplexProfile c t r) s :=
    congrArg (fun f : ℝ → ℂ => deriv f s) htfn
  have hlocal : monopoleWithRemoteRadiation c Z s =ᶠ[𝓝 r]
      monopoleInnerComplexProfile c s := by
    filter_upwards [Iio_mem_nhds hrR] with x hx
    simp only [monopoleWithRemoteRadiation, hZ s x hx.le, add_zero]
  have hL : complexRadialLaplacian (monopoleWithRemoteRadiation c Z s) r =
      complexRadialLaplacian (monopoleInnerComplexProfile c s) r := by
    unfold complexRadialLaplacian
    rw [hlocal.deriv.deriv_eq, hlocal.deriv_eq]
  have hD : complexRadialDilation (monopoleWithRemoteRadiation c Z s) r =
      complexRadialDilation (monopoleInnerComplexProfile c s) r := by
    unfold complexRadialDilation
    rw [hlocal.eq_of_nhds, hlocal.deriv_eq]
  unfold complexRadialRenormalizedResidual
  rw [ht, hL, hD]
  ring

/-- The exact full Hartree residual with remote complex radiation is
equal, in the positive core, to the previously defined *effective*
monopole residual with the artificial cubic replaced by the TRUE exterior
Hartree density potential. All nonlocal quartic cross terms are retained. -/
theorem actual_full_radial_residual_remote_eq_exterior_increment
    (c b omega : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {R s r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hsep : 2 * r ≤ R)
    (hZ : ∀ t rho, rho ≤ R → Z t rho = 0)
    (hVmeas : Measurable (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c s)) (c s)))
    (hZmeas : Measurable (Z s))
    (hF : IntegrableOn (remoteComplexQuarticDifference
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c s)) (c s)) (Z s)) (Ioi R))
    (hVrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(monopolePerturbedRadialProfile
          (monopoleQuadraticRadius (c s)) (c s) rho : ℂ)‖ ^ 4)
      (Ioi (0 : ℝ))) :
    complexRadialRenormalizedResidual
      (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
      complexRadialRenormalizedResidual
        (fun _ x => (bubble x : ℂ)) (b s) (omega s) s r =
      monopoleExteriorHartreeIncrement
        (remoteComplexQuarticDifference
          (monopolePerturbedRadialProfile
            (monopoleQuadraticRadius (c s)) (c s)) (Z s))
        R c b omega s r := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s)
  let F : ℝ → ℝ := remoteComplexQuarticDifference V (Z s)
  have hres := actual_full_radial_residual_remote_eq_nonlin
    c b omega Z hr hsep hZ
  have hn := actual_complexHartree_remote_quartic_source_exact
    V (Z s) hR hr hsep (hZ s) hVmeas hZmeas hF hVrow
  have hNonlin :
      complexRadialHartreeNonlinearity
        (monopoleWithRemoteRadiation c Z s) r -
        complexRadialHartreeNonlinearity (monopoleInnerComplexProfile c s) r =
      (radialHartreeExteriorPotential F R r : ℂ) *
        (monopoleInnerComplexProfile c s r) ^ 3 := by
    exact hn
  have hFull :
      complexRadialRenormalizedResidual
          (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r =
        complexRadialRenormalizedResidual
          (monopoleInnerComplexProfile c) (b s) (omega s) s r +
        (radialHartreeExteriorPotential F R r : ℂ) *
          (monopoleInnerComplexProfile c s r) ^ 3 := by
    calc
      _ = complexRadialRenormalizedResidual
          (monopoleInnerComplexProfile c) (b s) (omega s) s r +
          (complexRadialRenormalizedResidual
            (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
           complexRadialRenormalizedResidual
            (monopoleInnerComplexProfile c) (b s) (omega s) s r) := by ring
      _ = _ := by rw [hres, hNonlin]
  rw [hFull]
  unfold monopoleExteriorHartreeIncrement monopoleInnerComplexProfile
  ring

/-- Genuine Hartree FULL residual, including remote complex radiation,
differs from the effective monopole residual by a certified O(r²) potential
error IF the physical quartic moment equals the slow amplitude. The
nonlinear mass matching condition itself still needs to be solved by the
three-region Hartree profile construction. -/
theorem actual_full_radial_residual_remote_match_norm_le
    (c b omega : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {R s r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hsep : 2 * r ≤ R)
    (hZ : ∀ t rho, rho ≤ R → Z t rho = 0)
    (hVmeas : Measurable (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c s)) (c s)))
    (hZmeas : Measurable (Z s))
    (hF : IntegrableOn (remoteComplexQuarticDifference
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c s)) (c s)) (Z s)) (Ioi R))
    (hVrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(monopolePerturbedRadialProfile
          (monopoleQuadraticRadius (c s)) (c s) rho : ℂ)‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hc : |c s| ≤ 1)
    (hcenter : c s =
      radialHartreeExteriorCenter
        (remoteComplexQuarticDifference
          (monopolePerturbedRadialProfile
            (monopoleQuadraticRadius (c s)) (c s)) (Z s)) R) :
    ‖monopoleComplexEffectiveIncrement c (b s) (omega s) s r -
      (complexRadialRenormalizedResidual
        (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
       complexRadialRenormalizedResidual
         (fun _ x => (bubble x : ℂ)) (b s) (omega s) s r)‖ ≤
    (4 * Real.pi * hartreeKappa * r ^ 2 *
      ∫ rho in Ioi R,
        |remoteComplexQuarticDifference
          (monopolePerturbedRadialProfile
            (monopoleQuadraticRadius (c s)) (c s)) (Z s) rho| /
          rho ^ 2) * (1 + monopoleRadialBoundConstant) ^ 3 := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s)
  let F : ℝ → ℝ := remoteComplexQuarticDifference V (Z s)
  have hmatch := actual_full_radial_residual_remote_eq_exterior_increment
    c b omega Z hR hr hsep hZ hVmeas hZmeas hF hVrow
  rw [hmatch]
  exact monopoleEffective_actualExterior_residual_diff_norm_le
    F (remoteComplexQuarticDifference_measurable V (Z s) hVmeas hZmeas)
    c b omega s hF hR hr hsep hc hcenter

end HBL.TypeIIDynamicSelection
