import HBL.RadialHartreeMultipole
import HBL.MonopoleHartreeExpansion

/-!
# Actual quartic remote-density mechanism behind the monopole source

For a real radial inner profile V and a radial remote perturbation Z which
vanishes in the inner region r<=R, the change in the TRUE inverse-square
Hartree nonlinearity on 2r<=R is exactly the exterior Riesz potential of
the quartic density difference times V(r)^3.

No local cubic interaction has been inserted by hand. Its coefficient is
the actual integral of the remote quartic density difference. The error
is O(r^2) with an explicit weighted radial mass. This is a spatial source
lemma: time evolution and the exact PDE profile remain open.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole

/-- The *actual* quartic density difference caused by an exterior real
radiation profile. It retains every quartic cross term with the inner field. -/
def radialRemoteQuarticDifference (V Z : ℝ → ℝ) (rho : ℝ) : ℝ :=
  (V rho + Z rho) ^ 4 - V rho ^ 4

/-- Exterior support of the actual quartic density difference follows
from exterior support of Z, not from an assumed density cutoff. -/
theorem radialRemoteQuarticDifference_vanishes_in_core
    (V Z : ℝ → ℝ) {R : ℝ}
    (hZ : ∀ rho, rho ≤ R → Z rho = 0) :
    ∀ rho, rho ≤ R → radialRemoteQuarticDifference V Z rho = 0 := by
  intro rho hrho
  simp [radialRemoteQuarticDifference, hZ rho hrho]

/-- On the interior the original Hartree nonlinearity gets EXACTLY the
exterior Riesz potential times the inner cubic; no extra local term and no
approximated kernel. The only integrability assumptions are precisely the
two absolute radial source rows that occur in the actual integral. -/
theorem actual_radialHartree_remote_quartic_source_exact
    (V Z : ℝ → ℝ) {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hsep : 2 * r ≤ R)
    (hZ : ∀ rho, rho ≤ R → Z rho = 0)
    (hf : Measurable (radialRemoteQuarticDifference V Z))
    (hF : IntegrableOn (radialRemoteQuarticDifference V Z) (Ioi R))
    (hVrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * V rho ^ 4) (Ioi (0 : ℝ))) :
    radialHartreeNonlinearity (fun rho => V rho + Z rho) r -
      radialHartreeNonlinearity V r =
    radialHartreeExteriorPotential (radialRemoteQuarticDifference V Z) R r *
      V r ^ 3 := by
  let F := radialRemoteQuarticDifference V Z
  have hFzero : ∀ rho, rho ≤ R → F rho = 0 :=
    radialRemoteQuarticDifference_vanishes_in_core V Z hZ
  have hFindicator : (Ioi R).indicator F = F := by
    funext rho
    by_cases hh : rho ∈ Ioi R
    · simp [hh]
    · have hle : rho ≤ R := le_of_not_gt hh
      simp [hh, hFzero rho hle]
  have hPotF : radialHartreePotential F r =
      radialHartreeExteriorPotential F R r := by
    calc
      radialHartreePotential F r =
        radialHartreePotential ((Ioi R).indicator F) r := by rw [hFindicator]
      _ = _ := (radialHartreeExteriorPotential_eq_indicator
        F hR.le r).symm
  have hFrowOuter := (radialHartreeExteriorPotential_quadratic_center
    F hf hF hR hr hsep).2.1
  have hFrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi (0 : ℝ)) := by
    have heq : (fun rho => rho * hartreeRadialLog r rho * F rho) =
        (Ioi R).indicator
          (fun rho => rho * hartreeRadialLog r rho * F rho) := by
      funext rho
      by_cases hh : rho ∈ Ioi R
      · simp [hh]
      · have hle : rho ≤ R := le_of_not_gt hh
        simp [hh, hFzero rho hle]
    rw [heq]
    exact (hFrowOuter.integrable_indicator measurableSet_Ioi).integrableOn
  have hDensity : (fun rho => (V rho + Z rho) ^ 4) =
      (fun rho => V rho ^ 4 + F rho) := by
    funext rho
    dsimp [F, radialRemoteQuarticDifference]
    ring
  have hPotentialSum :
      radialHartreePotential (fun rho => (V rho + Z rho) ^ 4) r =
      radialHartreePotential (fun rho => V rho ^ 4) r +
        radialHartreeExteriorPotential F R r := by
    rw [hDensity]
    calc
      radialHartreePotential (fun rho => V rho ^ 4 + F rho) r =
          radialHartreePotential (fun rho => V rho ^ 4) r +
            radialHartreePotential F r := by
        unfold radialHartreePotential
        have heq : (fun rho => rho * hartreeRadialLog r rho *
            (V rho ^ 4 + F rho)) =
          (fun rho => rho * hartreeRadialLog r rho * V rho ^ 4) +
            (fun rho => rho * hartreeRadialLog r rho * F rho) := by
          funext rho
          simp only [Pi.add_apply]
          ring
        rw [heq, integral_add hVrow hFrow]
        ring
      _ = _ := by rw [hPotF]
  have hZr : Z r = 0 := hZ r (by linarith)
  unfold radialHartreeNonlinearity
  rw [hZr, add_zero, hPotentialSum]
  ring

/-- The first term of the actual *nonlocal* remote Hartree interaction is
a cubic potential with coefficient equal to the true exterior mass.
The complete error is O(r²) times the inner cubic, for any real V,Z
satisfying the actual integrability/support conditions above. -/
theorem actual_radialHartree_remote_center_error_le
    (V Z : ℝ → ℝ) {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hsep : 2 * r ≤ R)
    (hZ : ∀ rho, rho ≤ R → Z rho = 0)
    (hf : Measurable (radialRemoteQuarticDifference V Z))
    (hF : IntegrableOn (radialRemoteQuarticDifference V Z) (Ioi R))
    (hVrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * V rho ^ 4) (Ioi (0 : ℝ))) :
    |radialHartreeNonlinearity (fun rho => V rho + Z rho) r -
      radialHartreeNonlinearity V r -
      radialHartreeExteriorCenter (radialRemoteQuarticDifference V Z) R *
        V r ^ 3| ≤
    (4 * Real.pi * hartreeKappa * r ^ 2 *
      ∫ rho in Ioi R,
        |radialRemoteQuarticDifference V Z rho| / rho ^ 2) * |V r| ^ 3 := by
  let F := radialRemoteQuarticDifference V Z
  have hsource := actual_radialHartree_remote_quartic_source_exact
    V Z hR hr hsep hZ hf hF hVrow
  have hpot := (radialHartreeExteriorPotential_quadratic_center
    F hf hF hR hr hsep).2.2
  rw [hsource]
  have heq : radialHartreeExteriorPotential F R r * V r ^ 3 -
      radialHartreeExteriorCenter F R * V r ^ 3 =
      (radialHartreeExteriorPotential F R r -
        radialHartreeExteriorCenter F R) * V r ^ 3 := by ring
  rw [heq, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_right hpot (by positivity)

end HBL.TypeIIDynamicSelection
