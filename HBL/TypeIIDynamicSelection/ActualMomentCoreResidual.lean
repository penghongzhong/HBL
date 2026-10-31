import HBL.TypeIIDynamicSelection.ActualMomentProfileDynamics
import HBL.TypeIIDynamicSelection.ActualRadiation3DMoment
import Mathlib.Tactic

/-!
# Exact original Hartree monopole core residual with physical 3D radiation moment

The SAME original real moving monopole profile, the ACTUAL three-dimensional
inverse-square radiation centre, the ACTUAL renormalized residual, and its
true self-radiation Hartree Riesz source appear in these theorems.

Compared to the earlier core estimates for an arbitrary amplitude path,
its velocity is derived directly from the true 3D radiation moment.

This closes the core monopole/static and the pure-radiation self-density
source discrepancy. It does NOT yet estimate the mixed core-radiation
quartic terms, derive all minimal-weight atoms, prove any Fredholm/Kummer/
remote source cancellation, or establish an actual nonlinear blowup orbit.
The original manuscript 2.12 remains open.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The original actual Hartree radial core residual is quadratic modulo
the explicitly derived true physical 3D-moment time tangent and the two
real modulation speeds. No abstract amplitude velocity is supplied. -/
theorem actual_threeD_moment_monopole_core_effective_residual_quadratic
    (ell b omega : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    {s dm r : ℝ}
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hMoment3D : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t)) dm (time s))
    (hc : |actualPhysicalRadiationMonopole ell z time s| ≤ 1)
    (hr : 0 < r)
    (hcore : |actualPhysicalRadiationMonopole ell z time s| * r / 4 ≤ 1 / 2) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (actualPhysicalRadiationMonopole ell z time s))
        (actualPhysicalRadiationMonopole ell z time s) rho ^ 4)
      (Ioi (0 : ℝ)) ∧
    ‖monopoleComplexEffectiveIncrement
        (actualPhysicalRadiationMonopole ell z time) (b s) (omega s) s r -
      monopoleComplexCoreFirstOrder
        (actualPhysicalRadiationMonopole ell z time s)
        (-(b s * actualPhysicalRadiationMonopole ell z time s) +
          hartreeKappa * (ell s) ^ 3 * dm)
        (b s) (omega s) r‖ ≤
      monopoleStaticRadialBoundConstant *
        (actualPhysicalRadiationMonopole ell z time s) ^ 2 := by
  have hcoef := actual_physical_threeD_radiation_slow_coefficient_hasDerivAt
    ell b z time hEll hEllPos hTime hMoment3D
  exact monopoleComplexEffectiveIncrement_core_quadratic_control
    hcoef hc hr hcore (b s) (omega s)

/-- REAL physical Hartree self-radiation source, not an inserted
local cubic: the first-layer quadratic core residual and the physical
whole-radiation self-potential mismatch are controlled simultaneously.
The positive r² error follows from the genuine inverse-square Riesz
moment; all missing mixed-radiation terms remain explicitly outside
this theorem. -/
theorem actual_threeD_moment_monopole_self_Hartree_source_quadratic
    (ell b omega : ℝ → ℝ) (z Z : ℝ → ℝ → ℂ)
    (time : ℝ → ℝ) {s dm r M D : ℝ}
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hMoment3D : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t)) dm (time s))
    (hZphysical : Z s = rescalePhysicalRadiation (ell s) (z (time s)))
    (hZ : Measurable (Z s)) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbound : ∀ rho, 0 ≤ rho → ‖Z s rho‖ ≤ M)
    (hmass : IntegrableOn
      (fun rho => rho ^ 2 * ‖Z s rho‖ ^ 2) (Ioi (0 : ℝ)))
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 →
      ‖Z s rho - Z s 0‖ ≤ D * rho ^ 2)
    (hc : |actualPhysicalRadiationMonopole ell z time s| ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hcore : |actualPhysicalRadiationMonopole ell z time s| * r / 4 ≤ 1 / 2) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (actualPhysicalRadiationMonopole ell z time s))
        (actualPhysicalRadiationMonopole ell z time s) rho ^ 4)
      (Ioi (0 : ℝ)) ∧
    ‖actualWholeRadiationSelfCubicIncrement
        (actualPhysicalRadiationMonopole ell z time) b omega Z s r -
      monopoleComplexCoreFirstOrder
        (actualPhysicalRadiationMonopole ell z time s)
        (-(b s * actualPhysicalRadiationMonopole ell z time s) +
          hartreeKappa * (ell s) ^ 3 * dm)
        (b s) (omega s) r‖ ≤
      monopoleStaticRadialBoundConstant *
        (actualPhysicalRadiationMonopole ell z time s) ^ 2 +
      (radialHartreeCenterBoundConstant
        (fun rho => ‖Z s rho‖ ^ 4) (4 * M ^ 3 * D) * r ^ 2) *
        (1 + monopoleRadialBoundConstant) ^ 3 := by
  let c := actualPhysicalRadiationMonopole ell z time
  have hcoreQuadratic :=
    actual_threeD_moment_monopole_core_effective_residual_quadratic
      ell b omega z time hEll hEllPos hTime hMoment3D hc hr hcore
  have hCenter : c s = hartreeKappa * ell s *
      actualPhysicalInverseSquareMoment (z (time s)) := by
    exact actual_whole_radiation_center_eq_physical_threeD_moment
      (ell s) hEllPos (z (time s))
  have hSelf := actual_physical_threeD_whole_radiation_self_cubic_core_bound
    c b omega ell time z Z hEllPos hZphysical hCenter
    hZ hM hD hbound hmass hflat hc hr hr1
  refine ⟨hcoreQuadratic.1, ?_⟩
  let A : ℂ := monopoleComplexEffectiveIncrement c (b s) (omega s) s r
  let C : ℂ := actualWholeRadiationSelfCubicIncrement c b omega Z s r
  let F : ℂ := monopoleComplexCoreFirstOrder (c s)
    (-(b s * c s) + hartreeKappa * (ell s) ^ 3 * dm)
    (b s) (omega s) r
  have htriangle : ‖C-F‖ ≤ ‖A-C‖ + ‖A-F‖ := by
    calc
      ‖C-F‖ = ‖-(A-C)+(A-F)‖ := by congr 1; abel
      _ ≤ ‖-(A-C)‖ + ‖A-F‖ := norm_add_le _ _
      _ = ‖A-C‖ + ‖A-F‖ := by rw [norm_neg]
  have hSelf' : ‖A-C‖ ≤
      (radialHartreeCenterBoundConstant
        (fun rho => ‖Z s rho‖ ^ 4) (4 * M ^ 3 * D) * r ^ 2) *
        (1 + monopoleRadialBoundConstant) ^ 3 := hSelf
  have hCore' : ‖A-F‖ ≤
      monopoleStaticRadialBoundConstant * (c s) ^ 2 := hcoreQuadratic.2
  calc
    ‖C-F‖ ≤ ‖A-C‖ + ‖A-F‖ := htriangle
    _ ≤ (radialHartreeCenterBoundConstant
          (fun rho => ‖Z s rho‖ ^ 4) (4 * M ^ 3 * D) * r ^ 2) *
            (1 + monopoleRadialBoundConstant) ^ 3 +
          monopoleStaticRadialBoundConstant * (c s) ^ 2 :=
        add_le_add hSelf' hCore'
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
