import HBL.TypeIIDynamicSelection.ActualOneLayerTwoChannelPDE
import Mathlib.Tactic

/-!
# True-Hartree radiation PDE cancels every pure-radiation evolution source

Given one actual real core V and one actual complex Hartree radiation Z,
the full nonlocal source is the SAME exact renormalized PDE residual in
both H+ and H- channels. If Z solves its genuine renormalized Hartree
equation, its full time derivative, radial Laplacian, scaling/phase drift
and self-Hartree term cancel. Only three complete physical interaction
products survive; the local cubic multiplier and the entire mixed
quartic potential, not only their linearizations, are retained.

The assumption complexRadialRenormalizedResidual Z b omega s r = 0
is the *actual radiation PDE*, not a surrogate cancellation or
an assigned smallness/order hypothesis. Its realization from the cited
3D high-regularity Hartree flow, critical rescaling, physical clock
and radial representative is a separate analytical interface.

This is a strictly narrower result than original manuscript 2.12:
uniform weighted estimates, Kummer/remote matching and the positive
generated-order ledger remain OPEN. It does not set the blowup rate.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Exact NONLINEAR interaction of a true Hartree bubble profile
and its physical complex regular radiation. The three terms are:
full mixed Riesz density, pure-radiation potential acting on the
changed cubic, and bubble potential acting on the changed cubic. -/
def actualOneLayerInteractionOnly
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ) (s r : ℝ) : ℂ :=
  (radialHartreePotential
     (actualWholeRadiationMixedQuartic (V s) (Z s)) r : ℂ) *
       actualWholeRadiationLocalCubic
         (fun rho => (V s rho : ℂ) + Z s rho) r +
  (radialHartreePotential (fun rho => ‖Z s rho‖ ^ 4) r : ℂ) *
       (actualWholeRadiationLocalCubic
          (fun rho => (V s rho : ℂ) + Z s rho) r -
        actualWholeRadiationLocalCubic (Z s) r) +
  (radialHartreePotential
     (fun rho => ‖(V s rho : ℂ)‖ ^ 4) r : ℂ) *
       (actualWholeRadiationLocalCubic
          (fun rho => (V s rho : ℂ) + Z s rho) r -
        actualWholeRadiationLocalCubic
          (fun rho => (V s rho : ℂ)) r)

/-- The FULL genuine Hartree PDE residual, with radiation inserted,
reduces to its true bubble/radiation nonlocal interaction WHEN the
radiation satisfies its own renormalized Hartree PDE. In particular
no independent real or imaginary source is introduced. -/
theorem actual_one_layer_PDE_radiation_evolution_cancelled
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ)
    (hVTime : DifferentiableAt ℝ (fun t : ℝ => (V t r : ℂ)) s)
    (hZTime : DifferentiableAt ℝ (fun t : ℝ => Z t r) s)
    (hVSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (fun y : ℝ => (V s y : ℂ)) x)
    (hZSpace : ∀ x : ℝ, DifferentiableAt ℝ (Z s) x)
    (hVSecond : DifferentiableAt ℝ
      (deriv (fun y : ℝ => (V s y : ℂ))) r)
    (hZSecond : DifferentiableAt ℝ (deriv (Z s)) r)
    (hFullRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ) + Z s rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hCoreRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hRadiationRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖Z s rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hRadiationPDE :
      complexRadialRenormalizedResidual Z b omega s r = 0) :
    actualOneLayerCommonPDEResidual V Z b omega s r =
      actualOneLayerInteractionOnly V Z s r := by
  have hFull :
      actualOneLayerCommonPDEResidual V Z b omega s r =
        actualOneLayerFullHartreeForcing V Z b omega s r := by
    simpa only [actualOneLayerCommonPDEResidual,
      actualOneLayerFullHartreeForcing] using
      (actual_one_layer_full_renormalized_Hartree_PDE_source
        V Z b omega s r hVTime hZTime hVSpace hZSpace
        hVSecond hZSecond hFullRow hCoreRow hRadiationRow)
  have hZ :
      Complex.I * deriv (fun t : ℝ => Z t r) s +
      complexRadialLaplacian (Z s) r +
      Complex.I * (b : ℂ) * complexRadialDilation (Z s) r +
      (omega : ℂ) * Z s r +
      (radialHartreePotential (fun rho => ‖Z s rho‖ ^ 4) r : ℂ) *
        actualWholeRadiationLocalCubic (Z s) r = 0 := by
    simp only [complexRadialRenormalizedResidual,
      complexRadialHartreeNonlinearity, actualWholeRadiationLocalCubic]
      at hRadiationPDE ⊢
    linear_combination hRadiationPDE
  calc
    actualOneLayerCommonPDEResidual V Z b omega s r =
        actualOneLayerFullHartreeForcing V Z b omega s r := hFull
    _ = actualOneLayerInteractionOnly V Z s r := by
      unfold actualOneLayerFullHartreeForcing actualOneLayerInteractionOnly
      push_cast
      linear_combination hZ

/-- TRUE real and phase Hartree interactions result from applying the
two projections to the SAME solved radiation PDE residual. This
is the source which must next satisfy original weighted H+/H- bounds. -/
theorem actual_one_layer_PDE_both_channels_interaction_only
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ)
    (hVTime : DifferentiableAt ℝ (fun t : ℝ => (V t r : ℂ)) s)
    (hZTime : DifferentiableAt ℝ (fun t : ℝ => Z t r) s)
    (hVSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (fun y : ℝ => (V s y : ℂ)) x)
    (hZSpace : ∀ x : ℝ, DifferentiableAt ℝ (Z s) x)
    (hVSecond : DifferentiableAt ℝ
      (deriv (fun y : ℝ => (V s y : ℂ))) r)
    (hZSecond : DifferentiableAt ℝ (deriv (Z s)) r)
    (hFullRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ) + Z s rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hCoreRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hRadiationRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖Z s rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hRadiationPDE :
      complexRadialRenormalizedResidual Z b omega s r = 0) :
    actualOneLayerPlusPDE V Z b omega s r =
        (actualOneLayerInteractionOnly V Z s r).re ∧
    actualOneLayerMinusPDE V Z b omega s r =
        (actualOneLayerInteractionOnly V Z s r).im := by
  have h := actual_one_layer_PDE_radiation_evolution_cancelled
      V Z b omega s r hVTime hZTime hVSpace hZSpace
      hVSecond hZSecond hFullRow hCoreRow hRadiationRow hRadiationPDE
  exact ⟨congrArg Complex.re h, congrArg Complex.im h⟩

end HBL.TypeIIDynamicSelection
