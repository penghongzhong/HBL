import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# True critical-scale covariance of the 3D radial inverse-square Hartree potential

The physical regular radiation in the original Type-II manuscript is
Z_ell(r) = sqrt(ell) * z(ell*r).  Its quartic center moment scales as ell;
its *quadratic-density Riesz potential*, which enters the nonlinear mixed
source envelope, is scale invariant after moving the observation point.

These identities use the ACTUAL half-line inverse-square Hartree
logarithmic kernel. They involve neither a remote-support approximation
nor a postulated terminal blowup exponent.

The final uniform potential estimate follows from the already strictly
verified bubble-squared Riesz domination for the physical radiation z.
The displayed physical radial decay is a genuine input on the regular
radiation and must still be supplied by the PDE profile construction.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

/-- Physical energy-critical radiation produces exactly one power of the
length ell in the quadratic amplitude, without imposing a rate. -/
theorem physicalRadiation_rescale_quadratic
    (ell : ℝ) (hell : 0 < ell) (z : ℝ → ℂ) (rho : ℝ) :
    ‖rescalePhysicalRadiation ell z rho‖ ^ 2 =
      ell * ‖z (ell * rho)‖ ^ 2 := by
  unfold rescalePhysicalRadiation
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg ell), mul_pow,
    Real.sq_sqrt hell.le]

/-- The actual logarithmic angular kernel is homogeneous of degree zero.
The division is totalized at its null diagonal; this algebraic
identity remains valid there without introducing an axiom. -/
theorem physicalRadiation_hartree_log_scale
    (ell r rho : ℝ) (hell : 0 < ell) :
    hartreeRadialLog r rho =
      hartreeRadialLog (ell * r) (ell * rho) := by
  unfold hartreeRadialLog
  congr 1
  rw [show ell * r + ell * rho = ell * (r + rho) by ring,
      show ell * r - ell * rho = ell * (r - rho) by ring,
      abs_mul, abs_of_pos hell]
  exact (mul_div_mul_left (r + rho) |r - rho| hell.ne').symm

/-- Exact covariance of the physical weighted Hartree half-line
integral. It is a change of variable in the REAL physical Riesz row,
not a new integral defined to force the conclusion. -/
theorem physicalRadiation_quadratic_Riesz_row_scale
    (ell : ℝ) (hell : 0 < ell) (r : ℝ) (z : ℝ → ℂ) :
    (∫ rho in Ioi (0 : ℝ),
      rho * hartreeRadialLog r rho *
        ‖rescalePhysicalRadiation ell z rho‖ ^ 2) =
    ell⁻¹ * (∫ u in Ioi (0 : ℝ),
      u * hartreeRadialLog (ell * r) u * ‖z u‖ ^ 2) := by
  have hp (rho : ℝ) :
      rho * hartreeRadialLog r rho *
        ‖rescalePhysicalRadiation ell z rho‖ ^ 2 =
      (ell * rho) * hartreeRadialLog (ell * r) (ell * rho) *
        ‖z (ell * rho)‖ ^ 2 := by
    rw [physicalRadiation_rescale_quadratic ell hell z rho,
      physicalRadiation_hartree_log_scale ell r rho hell]
    ring
  calc
    _ = ∫ rho in Ioi (0 : ℝ),
      (ell * rho) * hartreeRadialLog (ell * r) (ell * rho) *
        ‖z (ell * rho)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with rho
        exact hp rho
    _ = ell⁻¹ * (∫ u in Ioi (0 : ℝ),
      u * hartreeRadialLog (ell * r) u * ‖z u‖ ^ 2) := by
        simpa only [mul_zero, smul_eq_mul] using
          (integral_comp_mul_left_Ioi
            (fun u : ℝ =>
              u * hartreeRadialLog (ell * r) u * ‖z u‖ ^ 2)
            0 hell)

/-- The full physical radial inverse-square Riesz operator on
quadratic radiation density is SCALE INVARIANT, with observation
radius transformed by ell. This is NOT a fixed terminal power. -/
theorem physicalRadiation_quadratic_Riesz_scale
    (ell : ℝ) (hell : 0 < ell) (r : ℝ) (hr : 0 < r)
    (z : ℝ → ℂ) :
    radialHartreePotential
      (fun rho => ‖rescalePhysicalRadiation ell z rho‖ ^ 2) r =
    radialHartreePotential (fun rho => ‖z rho‖ ^ 2) (ell * r) := by
  unfold radialHartreePotential
  rw [physicalRadiation_quadratic_Riesz_row_scale ell hell r z]
  field_simp [hell.ne', hr.ne']

/-- The genuine physical radiation has an observation-radius UNIFORM
quadratic-density Hartree potential if the ORIGINAL regular radiation
has a bubble-squared envelope. This is a concrete sufficient spatial
regularity condition, not an abstract weighted Riesz-row hypothesis. -/
theorem physicalRadiation_quadratic_Riesz_uniform_of_profile
    (ell : ℝ) (hell : 0 < ell) (r : ℝ) (hr : 0 < r)
    (z : ℝ → ℂ) (hz : Measurable z)
    {M : ℝ} (hM : 0 ≤ M)
    (hdecay : ∀ rho : ℝ, 0 < rho →
      ‖z rho‖ ^ 2 ≤ M * bubble rho ^ 2) :
    |radialHartreePotential
      (fun rho => ‖rescalePhysicalRadiation ell z rho‖ ^ 2) r| ≤
        radialHartreeRowBoundConstant * M := by
  rw [physicalRadiation_quadratic_Riesz_scale ell hell r hr z]
  have hsource : Measurable (fun rho => ‖z rho‖ ^ 2) :=
    hz.norm.pow_const 2
  have hpoint : ∀ rho : ℝ, 0 < rho →
      |‖z rho‖ ^ 2| ≤ M * bubble rho ^ 2 := by
    intro rho hpos
    rw [abs_of_nonneg (sq_nonneg (‖z rho‖))]
    exact hdecay rho hpos
  exact (radialHartreePotential_bubble_sq_domination
    (fun rho => ‖z rho‖ ^ 2) hsource hM hpoint
    (mul_pos hell hr)).2

/-- Directly discharge the r-normalized PHYSICAL Riesz-row
bound for the rescaled regular radiation, using the ALREADY PROVED
bubble-squared logarithmic row. This is a concrete spatial control,
not a hypothesis that the target radial Hartree potential is bounded.

The radial profile z satisfies the visible (Schwartz-compatible)
pointwise weighted condition. The length ell>0 is arbitrary and is
not tied to a prespecified blowup speed. -/
theorem physicalRadiation_quadratic_Riesz_row_uniform_of_profile
    (ell : ℝ) (hell : 0 < ell) (r : ℝ) (hr : 0 < r)
    (z : ℝ → ℂ) (hz : Measurable z)
    {M : ℝ} (hM : 0 ≤ M)
    (hdecay : ∀ rho : ℝ, 0 < rho →
      ‖z rho‖ ^ 2 ≤ M * bubble rho ^ 2) :
    (∫ rho in Ioi (0 : ℝ),
      rho * hartreeRadialLog r rho *
        ‖rescalePhysicalRadiation ell z rho‖ ^ 2) ≤
      r * radialHartreeBubbleBoundConstant * M := by
  have hpos : 0 < ell * r := mul_pos hell hr
  have hSource : Measurable (fun u => ‖z u‖ ^ 2) :=
    hz.norm.pow_const 2
  have hSourceBound : ∀ u : ℝ, 0 < u →
      |‖z u‖ ^ 2| ≤ M * bubble u ^ 2 := by
    intro u hu
    rw [abs_of_nonneg (sq_nonneg (‖z u‖))]
    exact hdecay u hu
  have hSourceRow :=
    radialHartreePotential_bubble_sq_domination
      (fun u => ‖z u‖ ^ 2) hSource hM hSourceBound hpos
  have hBubbleRow := radialHartreeBubble_integrable_bound hpos
  have hPoint (u : ℝ) (hu : 0 < u) :
      u * hartreeRadialLog (ell * r) u * ‖z u‖ ^ 2 ≤
        M * (u * hartreeRadialLog (ell * r) u * bubble u ^ 2) := by
    have hlog : 0 ≤ hartreeRadialLog (ell * r) u :=
      hartreeRadialLog_nonneg (ell * r) u hpos hu
    calc
      _ ≤ (u * hartreeRadialLog (ell * r) u) *
          (M * bubble u ^ 2) :=
        mul_le_mul_of_nonneg_left (hdecay u hu)
          (mul_nonneg hu.le hlog)
      _ = _ := by ring
  have hPhysicalRow :
      (∫ u in Ioi (0 : ℝ),
        u * hartreeRadialLog (ell * r) u * ‖z u‖ ^ 2) ≤
          (ell * r) * radialHartreeBubbleBoundConstant * M := by
    calc
      _ ≤ ∫ u in Ioi (0 : ℝ),
          M * (u * hartreeRadialLog (ell * r) u *
            bubble u ^ 2) := by
        apply integral_mono_ae hSourceRow.1 (hBubbleRow.1.const_mul M)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact hPoint u hu
      _ = M * (∫ u in Ioi (0 : ℝ),
          u * hartreeRadialLog (ell * r) u * bubble u ^ 2) := by
        rw [integral_const_mul]
      _ ≤ M * ((ell * r) * radialHartreeBubbleBoundConstant) :=
        mul_le_mul_of_nonneg_left hBubbleRow.2 hM
      _ = (ell * r) * radialHartreeBubbleBoundConstant * M := by
        ring
  rw [physicalRadiation_quadratic_Riesz_row_scale ell hell r z]
  calc
    ell⁻¹ * (∫ u in Ioi (0 : ℝ),
        u * hartreeRadialLog (ell * r) u * ‖z u‖ ^ 2) ≤
      ell⁻¹ * ((ell * r) * radialHartreeBubbleBoundConstant * M) :=
        mul_le_mul_of_nonneg_left hPhysicalRow (inv_nonneg.mpr hell.le)
    _ = r * radialHartreeBubbleBoundConstant * M := by
      field_simp [hell.ne']

/-- Genuine Lebesgue integrability of the energy-critical rescaled
regular-radiation inverse-square Hartree kernel row.  The original
physical profile has a directly checkable bubble-squared majorant;
integrability of the scaled row is DERIVED, not imposed, via the
pinned Mathlib theorem integrableOn_Ioi_comp_mul_left_iff. -/
theorem physicalRadiation_quadratic_Riesz_row_integrable_of_profile
    (ell : ℝ) (hell : 0 < ell) (r : ℝ) (hr : 0 < r)
    (z : ℝ → ℂ) (hz : Measurable z)
    {M : ℝ} (hM : 0 ≤ M)
    (hdecay : ∀ rho : ℝ, 0 < rho →
      ‖z rho‖ ^ 2 ≤ M * bubble rho ^ 2) :
    IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖rescalePhysicalRadiation ell z rho‖ ^ 2)
      (Ioi (0 : ℝ)) := by
  have hSource : Measurable (fun u => ‖z u‖ ^ 2) :=
    hz.norm.pow_const 2
  have hSourceBound : ∀ u : ℝ, 0 < u →
      |‖z u‖ ^ 2| ≤ M * bubble u ^ 2 := by
    intro u hu
    rw [abs_of_nonneg (sq_nonneg (‖z u‖))]
    exact hdecay u hu
  have hPhysical : IntegrableOn
      (fun u => u * hartreeRadialLog (ell * r) u * ‖z u‖ ^ 2)
      (Ioi (0 : ℝ)) :=
    (radialHartreePotential_bubble_sq_domination
      (fun u => ‖z u‖ ^ 2) hSource hM hSourceBound
        (mul_pos hell hr)).1
  have hScaled : IntegrableOn
      (fun rho => (ell * rho) *
        hartreeRadialLog (ell * r) (ell * rho) *
          ‖z (ell * rho)‖ ^ 2) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ =>
        u * hartreeRadialLog (ell * r) u * ‖z u‖ ^ 2)
      0 hell).2 (by simpa only [mul_zero] using hPhysical)
    simpa only [mul_zero] using h
  have hPoint : (fun rho =>
        rho * hartreeRadialLog r rho *
          ‖rescalePhysicalRadiation ell z rho‖ ^ 2) =
      (fun rho =>
        (ell * rho) * hartreeRadialLog (ell * r) (ell * rho) *
          ‖z (ell * rho)‖ ^ 2) := by
    funext rho
    rw [physicalRadiation_rescale_quadratic ell hell z rho,
        physicalRadiation_hartree_log_scale ell r rho hell]
    ring
  rw [hPoint]
  exact hScaled

end HBL.TypeIIDynamicSelection
