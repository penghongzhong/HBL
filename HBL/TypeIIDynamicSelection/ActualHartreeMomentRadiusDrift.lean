import HBL.TypeIIDynamicSelection.ActualHartreeMomentRadiusWindow
import HBL.TypeIIDynamicSelection.ActualMomentTransportGain
import Mathlib.Tactic

/-!
# Actual Hartree moment-moving cutoff radius derivative from the PDE clock

The genuine physical inverse-square quartic moment m(t) fixes
  R(s) = 4/(kappa_H * ell(s) * m(t(s))).
For ell_s=-b*ell, t_s=ell^2 and a true physical moment time
derivative m'(t)=dm, the exact radius identity is
  R_s/R-b = -ell^2 * dm/m.
This is derived from the physical moment flow and scalar chain rule,
not posited as a modulation-gain assumption. It closes the sole
remaining transport coefficient in the single-PDE cutoff residual.
The subsequent step must bound dm/m along the selected strong Hartree
flow; terminal moment positivity and its PDE flux are in existing files.

Nothing here assumes the Type II concentration exponent or proves
the full original 2.12 source cancellation.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The real physical Hartree moment determines the entire moving
cutoff radius at each time, with no arbitrary regional radius. -/
def actualPhysicalHartreeMomentRadius
    (ell : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    (s : ℝ) : ℝ :=
  actualHartreeMomentCutoffRadius (ell s)
    (radialPhysicalQuarticMoment (z (time s)))

/-- Differentiation of the *actual* inverse-square Hartree moment
cutoff yields its precise material cancellation. No unproved
source-order hypothesis is introduced. -/
theorem actual_Hartree_physical_moment_radius_drift_exact
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (time : ℝ → ℝ) (s dm : ℝ)
    (hell : 0 < ell s)
    (hm : 0 < radialPhysicalQuarticMoment (z (time s)))
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hMoment : HasDerivAt
      (fun t => radialPhysicalQuarticMoment (z t)) dm (time s)) :
    ∃ Rs : ℝ,
      HasDerivAt (actualPhysicalHartreeMomentRadius ell z time) Rs s ∧
      Rs / actualPhysicalHartreeMomentRadius ell z time s - b s =
        -((ell s) ^ 2 * (dm /
          radialPhysicalQuarticMoment (z (time s)))) := by
  let m : ℝ := radialPhysicalQuarticMoment (z (time s))
  have hk : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hdpos : 0 < hartreeKappa * ell s * m := by
    dsimp [m]
    positivity
  have hD : HasDerivAt
      (fun t => hartreeKappa * ell t *
        radialPhysicalQuarticMoment (z (time t)))
      (hartreeKappa * (-(b s * ell s)) * m +
        (hartreeKappa * ell s) * (dm * (ell s)^2)) s := by
    convert ((hEll.const_mul hartreeKappa).mul
      (hMoment.comp s hTime)) using 1
    · funext t
      simp only [Pi.mul_apply, Function.comp_apply]
    · dsimp [m]
  let d : ℝ :=
    hartreeKappa * (-(b s * ell s)) * m +
      (hartreeKappa * ell s) * (dm * (ell s)^2)
  let Rs : ℝ := -(4 * d) / (hartreeKappa * ell s * m) ^ 2
  have hRbase :=
    (hasDerivAt_const s (4 : ℝ)).div hD hdpos.ne'
  have hR :
      HasDerivAt (actualPhysicalHartreeMomentRadius ell z time) Rs s := by
    convert hRbase using 1
    · funext t
      rfl
    · dsimp [Rs, d, m]
      ring
  refine ⟨Rs,hR,?_⟩
  dsimp [Rs,d,m,actualPhysicalHartreeMomentRadius,
    actualHartreeMomentCutoffRadius]
  field_simp [hell.ne', hk.ne', hm.ne']; ring

end HBL.TypeIIDynamicSelection
