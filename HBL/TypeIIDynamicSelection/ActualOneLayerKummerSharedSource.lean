import HBL.TypeIIDynamicSelection.ActualOneLayerRadiationPDECancellation
import HBL.TypeIIDynamicSelection.ActualOneLayerKummerModulation
import Mathlib.Tactic

/-!
# Original 2.12: one ACTUAL Hartree PDE source for both inner channels
# and the parameter-dependent Kummer annulus

No abstract Kummer-region source is assigned. The original existing
Kummer source is literally the same complete Hartree PDE residual whose
real and imaginary components define the two physical Fredholm inputs.

When the regular radiation obeys its *genuine* renormalized Hartree
equation, that annular source is provably the complete three-term
nonlinear cross interaction (not an abstract source with prescribed
decay). The certified parameter-dependent Kummer inverse therefore
acts on the SAME physical interaction used by the inner H+/H- channels.

The radial PDE source integrability, high-regularity flow realization,
Kummer-to-inner/remote boundary matching, and complete positive-order
ledger remain necessary before original 2.12 can be accepted.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Profile.Kummer HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Source coherence BEFORE any regional solve: the Kummer source's
two real coordinates are exactly the previously defined H+/H-
actual PDE projections at the SAME spatial position. -/
theorem actual_one_layer_Kummer_and_inner_channels_same_PDE
    {z d : ℝ}
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega : ℝ → ℝ) (s : ℝ)
    (hcontinuous : Continuous (fun r : PhysicalAnnulus z d =>
      complexRadialRenormalizedResidual
        (fun t x => (V t x : ℂ) + Z t x) (b s) (omega s) s r.val -
      complexRadialRenormalizedResidual
        (fun t x => (V t x : ℂ)) (b s) (omega s) s r.val)) :
    ∀ r : PhysicalAnnulus z d,
      (actualHartreePDEResidualAnnulusSource
        V Z b omega s hcontinuous r).re =
          actualOneLayerPlusPDE V Z (b s) (omega s) s r.val ∧
      (actualHartreePDEResidualAnnulusSource
        V Z b omega s hcontinuous r).im =
          actualOneLayerMinusPDE V Z (b s) (omega s) s r.val := by
  intro r
  exact ⟨rfl, rfl⟩

/-- When the genuine radiation PDE is imposed, the Kummer C(annulus)
source equals the SAME nonlinear interaction already extracted from
the real/imaginary channel source. Continuity of the interaction
is DERIVED by extensional equality with the physical residual. -/
theorem actual_one_layer_Kummer_uses_exact_PDE_interaction
    {z d : ℝ}
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega : ℝ → ℝ) (s : ℝ)
    (hcontinuous : Continuous (fun r : PhysicalAnnulus z d =>
      complexRadialRenormalizedResidual
        (fun t x => (V t x : ℂ) + Z t x) (b s) (omega s) s r.val -
      complexRadialRenormalizedResidual
        (fun t x => (V t x : ℂ)) (b s) (omega s) s r.val))
    (hVTime : ∀ r : PhysicalAnnulus z d,
      DifferentiableAt ℝ (fun t : ℝ => (V t r.val : ℂ)) s)
    (hZTime : ∀ r : PhysicalAnnulus z d,
      DifferentiableAt ℝ (fun t : ℝ => Z t r.val) s)
    (hVSpace : ∀ r : PhysicalAnnulus z d, ∀ x : ℝ,
      DifferentiableAt ℝ (fun y : ℝ => (V s y : ℂ)) x)
    (hZSpace : ∀ r : PhysicalAnnulus z d, ∀ x : ℝ,
      DifferentiableAt ℝ (Z s) x)
    (hVSecond : ∀ r : PhysicalAnnulus z d,
      DifferentiableAt ℝ
        (deriv (fun y : ℝ => (V s y : ℂ))) r.val)
    (hZSecond : ∀ r : PhysicalAnnulus z d,
      DifferentiableAt ℝ (deriv (Z s)) r.val)
    (hFullRow : ∀ r : PhysicalAnnulus z d,
      MeasureTheory.IntegrableOn
        (fun rho => rho * hartreeRadialLog r.val rho *
          ‖(V s rho : ℂ) + Z s rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hCoreRow : ∀ r : PhysicalAnnulus z d,
      MeasureTheory.IntegrableOn
        (fun rho => rho * hartreeRadialLog r.val rho *
          ‖(V s rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hRadiationRow : ∀ r : PhysicalAnnulus z d,
      MeasureTheory.IntegrableOn
        (fun rho => rho * hartreeRadialLog r.val rho *
          ‖Z s rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hRadiationPDE : ∀ r : PhysicalAnnulus z d,
      complexRadialRenormalizedResidual Z (b s) (omega s) s r.val = 0) :
    ∃ hInteractionContinuous :
      Continuous (fun r : PhysicalAnnulus z d =>
        actualOneLayerInteractionOnly V Z s r.val),
      actualHartreePDEResidualAnnulusSource V Z b omega s hcontinuous =
        ⟨fun r : PhysicalAnnulus z d =>
            actualOneLayerInteractionOnly V Z s r.val,
          hInteractionContinuous⟩ := by
  have hpoint (r : PhysicalAnnulus z d) :
      actualOneLayerCommonPDEResidual V Z (b s) (omega s) s r.val =
        actualOneLayerInteractionOnly V Z s r.val :=
    actual_one_layer_PDE_radiation_evolution_cancelled
      V Z (b s) (omega s) s r.val
      (hVTime r) (hZTime r) (hVSpace r) (hZSpace r)
      (hVSecond r) (hZSecond r)
      (hFullRow r) (hCoreRow r) (hRadiationRow r)
      (hRadiationPDE r)
  have heq :
      (fun r : PhysicalAnnulus z d =>
        actualOneLayerInteractionOnly V Z s r.val) =
      (fun r : PhysicalAnnulus z d =>
        complexRadialRenormalizedResidual
          (fun t x => (V t x : ℂ) + Z t x)
            (b s) (omega s) s r.val -
        complexRadialRenormalizedResidual
          (fun t x => (V t x : ℂ)) (b s) (omega s) s r.val) := by
    funext r
    exact (hpoint r).symm
  have hInt : Continuous (fun r : PhysicalAnnulus z d =>
      actualOneLayerInteractionOnly V Z s r.val) := by
    rw [heq]
    exact hcontinuous
  refine ⟨hInt, ?_⟩
  ext r
  exact hpoint r

/-- The actual Kummer parameter inverse acts on precisely the
same PDE interaction as both Fredholm channels, not a prescribed
placeholder source. This is exact source matching, not the remaining
inner/annulus boundary-jet matching. -/
theorem actual_one_layer_Kummer_inverse_source_coherent
    {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d)
    (delta : ℂ)
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega : ℝ → ℝ) (s : ℝ)
    (hcontinuous : Continuous (fun r : PhysicalAnnulus z d =>
      complexRadialRenormalizedResidual
        (fun t x => (V t x : ℂ) + Z t x) (b s) (omega s) s r.val -
      complexRadialRenormalizedResidual
        (fun t x => (V t x : ℂ)) (b s) (omega s) s r.val))
    (hVTime : ∀ r : PhysicalAnnulus z d,
      DifferentiableAt ℝ (fun t : ℝ => (V t r.val : ℂ)) s)
    (hZTime : ∀ r : PhysicalAnnulus z d,
      DifferentiableAt ℝ (fun t : ℝ => Z t r.val) s)
    (hVSpace : ∀ r : PhysicalAnnulus z d, ∀ x : ℝ,
      DifferentiableAt ℝ (fun y : ℝ => (V s y : ℂ)) x)
    (hZSpace : ∀ r : PhysicalAnnulus z d, ∀ x : ℝ,
      DifferentiableAt ℝ (Z s) x)
    (hVSecond : ∀ r : PhysicalAnnulus z d,
      DifferentiableAt ℝ
        (deriv (fun y : ℝ => (V s y : ℂ))) r.val)
    (hZSecond : ∀ r : PhysicalAnnulus z d,
      DifferentiableAt ℝ (deriv (Z s)) r.val)
    (hFullRow : ∀ r : PhysicalAnnulus z d,
      MeasureTheory.IntegrableOn
        (fun rho => rho * hartreeRadialLog r.val rho *
          ‖(V s rho : ℂ) + Z s rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hCoreRow : ∀ r : PhysicalAnnulus z d,
      MeasureTheory.IntegrableOn
        (fun rho => rho * hartreeRadialLog r.val rho *
          ‖(V s rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hRadiationRow : ∀ r : PhysicalAnnulus z d,
      MeasureTheory.IntegrableOn
        (fun rho => rho * hartreeRadialLog r.val rho *
          ‖Z s rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hRadiationPDE : ∀ r : PhysicalAnnulus z d,
      complexRadialRenormalizedResidual Z (b s) (omega s) s r.val = 0) :
    ∃ hInteractionContinuous :
      Continuous (fun r : PhysicalAnnulus z d =>
        actualOneLayerInteractionOnly V Z s r.val),
      annulusParameterInverse T delta
          (actualHartreePDEResidualAnnulusSource
            V Z b omega s hcontinuous) =
        annulusParameterInverse T delta
          (⟨fun r : PhysicalAnnulus z d =>
              actualOneLayerInteractionOnly V Z s r.val,
            hInteractionContinuous⟩ : AnnulusSource z d) := by
  obtain ⟨hInt, hSource⟩ :=
    actual_one_layer_Kummer_uses_exact_PDE_interaction
      V Z b omega s hcontinuous
      hVTime hZTime hVSpace hZSpace hVSecond hZSecond
      hFullRow hCoreRow hRadiationRow hRadiationPDE
  refine ⟨hInt, ?_⟩
  rw [hSource]

end HBL.TypeIIDynamicSelection
