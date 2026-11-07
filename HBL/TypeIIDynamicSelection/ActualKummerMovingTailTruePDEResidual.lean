import HBL.TypeIIDynamicSelection.ActualComplexMovingRemoteMatch
import HBL.TypeIIDynamicSelection.ActualKummerRepairFullDensityFeedback
import Mathlib.Tactic

/-!
# Exact true-Hartree PDE core source of the moving Kummer replacement tail

Define the exterior Kummer repair as the literal physical interface repair
restricted to the original annulus (a(t) R,2 a(t) R]. In the interior
r < a(s) R, the entire renormalized PDE residual difference equals the
nonlocal Hartree density feedback: time derivative, Laplacian, dilation and
phase differences vanish by local-in-time and local-in-space equality.

The density difference is exactly the full quartic physical correction,
not an assigned source atom or a pure D^4 proxy. The endpoint C1 gluing
with the selected interior Kummer profile remains a separate obligation.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual physical Kummer tail used ONLY on its replacement annulus,
rather than extending its affine polynomial into the bubble core. -/
def actualKummerPhysicalOuterRepair
    (a : ℝ → ℝ) (R : ℝ) (p q : ℝ → ℂ) (t y : ℝ) : ℂ :=
  (Ioc (a t * R) (2 * a t * R)).indicator
    (actualKummerPhysicalInterfaceRepair (a t) R (p t) (q t)) y

theorem actual_Kummer_physical_outer_repair_zero_in_core
    (a : ℝ → ℝ) (R : ℝ) (p q : ℝ → ℂ)
    (t y : ℝ) (hy : y ≤ a t * R) :
    actualKummerPhysicalOuterRepair a R p q t y = 0 := by
  have hnot : y ∉ Ioc (a t * R) (2 * a t * R) := by
    intro hmem
    exact (not_lt_of_ge hy) hmem.1
  simp [actualKummerPhysicalOuterRepair, hnot]

/-- For an arbitrary continuously moving exterior perturbation, the full
renormalized Hartree residual has no LOCAL derivative discrepancy in the core.
No global smoothness of the exterior field at its interface is assumed. -/
theorem actual_complex_moving_exterior_full_PDE_residual_exact
    (R : ℝ → ℝ) (U Q : ℝ → ℝ → ℂ)
    (b omega s r : ℝ)
    (hRc : ContinuousAt R s)
    (hr : r < R s)
    (hQ : ∀ t y : ℝ, y ≤ R t → Q t y = 0) :
    complexRadialRenormalizedResidual
        (fun t y => U t y + Q t y) b omega s r -
      complexRadialRenormalizedResidual U b omega s r =
    complexRadialHartreeNonlinearity
        (fun y => U s y + Q s y) r -
      complexRadialHartreeNonlinearity (U s) r := by
  have htimeEq : (fun t => U t r + Q t r) =ᶠ[𝓝 s]
      (fun t => U t r) := by
    filter_upwards [moving_remote_cutoff_eventually_zero
      R Q hRc hr hQ] with t ht
    rw [ht, add_zero]
  have ht : deriv (fun t => U t r + Q t r) s =
      deriv (fun t => U t r) s :=
    htimeEq.deriv_eq
  have hsp : (fun y => U s y + Q s y) =ᶠ[𝓝 r] U s := by
    filter_upwards [Iio_mem_nhds hr] with y hy
    rw [hQ s y hy.le, add_zero]
  have hL : complexRadialLaplacian
      (fun y => U s y + Q s y) r =
      complexRadialLaplacian (U s) r := by
    unfold complexRadialLaplacian
    rw [hsp.deriv.deriv_eq, hsp.deriv_eq]
  have hPoint : Q s r = 0 := hQ s r hr.le
  have hD : complexRadialDilation
      (fun y => U s y + Q s y) r =
      complexRadialDilation (U s) r := by
    unfold complexRadialDilation
    change (U s r + Q s r) / 2 +
      (r : ℂ) * deriv (fun y => U s y + Q s y) r =
      U s r / 2 + (r : ℂ) * deriv (U s) r
    rw [hPoint, add_zero, hsp.deriv_eq]
  unfold complexRadialRenormalizedResidual
  rw [ht, hL, hD]
  simp only [hPoint, add_zero]
  ring

/-- The full real quartic density of the concrete moving repair is
literally the already estimated localized Hartree density difference. -/
theorem actual_Kummer_moving_repair_density_equals_real_PDE_density
    (a : ℝ → ℝ) (R : ℝ) (p q : ℝ → ℂ)
    (U : ℝ → ℝ → ℂ) (s : ℝ) :
    actualComplexRemoteDensity (U s)
        (actualKummerPhysicalOuterRepair a R p q s) =
      actualKummerPhysicalRepairOuterDensityDifference
        (U s) (a s) R (p s) (q s) := by
  funext y
  by_cases hy : y ∈ Ioc (a s * R) (2 * a s * R)
  · simp [actualComplexRemoteDensity,
      actualKummerPhysicalOuterRepair,
      actualKummerPhysicalRepairOuterDensityDifference, hy]
  · simp [actualComplexRemoteDensity,
      actualKummerPhysicalOuterRepair,
      actualKummerPhysicalRepairOuterDensityDifference, hy]

/-- The moving physical Kummer repair produces exactly the full Hartree
outer-source term in the bubble core, with NO independent a_t, p_t or q_t
forcing there. The source and its L1 integrability are DERIVED from the
actual repair and its pointwise shell envelope. -/
theorem actual_Kummer_moving_repair_true_Hartree_core_PDE_source_exact
    (a : ℝ → ℝ) (R : ℝ) (p q : ℝ → ℂ)
    (U : ℝ → ℝ → ℂ) (b omega s r M : ℝ)
    (ha : ∀ t : ℝ, 0 < a t)
    (haCont : ContinuousAt a s) (hR : 0 < R)
    (hM : 0 ≤ M)
    (hr : 0 < r) (hsep : 2 * r ≤ a s * R)
    (hUmeas : Measurable (U s))
    (hUrow : IntegrableOn
      (fun y => y * hartreeRadialLog r y * ‖U s y‖ ^ 4)
        (Ioi (0 : ℝ)))
    (hUShell : ∀ y ∈ Ioc (a s * R) (2 * a s * R),
      ‖U s y‖ ≤ M) :
    complexRadialRenormalizedResidual
        (fun t y => U t y + actualKummerPhysicalOuterRepair a R p q t y)
        b omega s r -
      complexRadialRenormalizedResidual U b omega s r =
      (radialHartreeExteriorPotential
        (actualKummerPhysicalRepairOuterDensityDifference
          (U s) (a s) R (p s) (q s)) (a s * R) r : ℂ) *
          actualWholeRadiationLocalCubic (U s) r := by
  let Q : ℝ → ℝ → ℂ :=
    actualKummerPhysicalOuterRepair a R p q
  let Rmove : ℝ → ℝ := fun t => a t * R
  have hRc : ContinuousAt Rmove s := by
    dsimp [Rmove]
    exact haCont.mul continuousAt_const
  have hrCore : r < Rmove s := by
    dsimp [Rmove]
    have hrR : 0 < a s * R := mul_pos (ha s) hR
    linarith
  have hQzero : ∀ t y : ℝ, y ≤ Rmove t → Q t y = 0 := by
    intro t y hy
    exact actual_Kummer_physical_outer_repair_zero_in_core
      a R p q t y hy
  have hMove :=
    actual_complex_moving_exterior_full_PDE_residual_exact
      Rmove U Q b omega s r hRc hrCore hQzero
  have hQmeas : Measurable (Q s) := by
    have hRepair : Continuous (actualKummerPhysicalInterfaceRepair
        (a s) R (p s) (q s)) := by
      rw [continuous_iff_continuousAt]
      intro y
      exact (actual_Kummer_physical_interface_repair_derivatives
        (a s) R y (ha s).ne' hR.ne' (p s) (q s)).1.continuousAt
    exact hRepair.measurable.indicator measurableSet_Ioc
  have hFint :=
    actual_Kummer_physical_repair_outer_density_difference_L1
      (U s) hUmeas (a s) R M (ha s) hR hM
      (p s) (q s) hUShell
  have hF :
      IntegrableOn
        (actualComplexRemoteDensity (U s) (Q s))
          (Ioi (a s * R)) := by
    rw [actual_Kummer_moving_repair_density_equals_real_PDE_density]
    exact hFint.1.integrableOn
  have hNonlin :=
    actual_complex_inner_remote_Hartree_source_exact
      (U s) (Q s) (mul_pos (ha s) hR) hr hsep
      (fun y hy => hQzero s y hy)
      hUmeas hQmeas hF hUrow
  have hFexact :=
    actual_Kummer_moving_repair_density_equals_real_PDE_density
      a R p q U s
  rw [hFexact] at hNonlin
  exact hMove.trans hNonlin

end HBL.TypeIIDynamicSelection
