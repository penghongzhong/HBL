import HBL.TypeIIDynamicSelection.ActualHartreeCriticalNonlinearityScaling
import HBL.TypeIIDynamicSelection.ActualOneLayerRadiationPDECancellation
import HBL.TypeIIDynamicSelection.ActualHartreeKummerChargeReference
import Mathlib.Tactic

/-!
# Exact critical scale transport of the ORIGINAL mixed Hartree interaction

The three nonlocal inverse-square quartic Riesz terms of
  Interaction(V,Z) = N(V+Z)-N(V)-N(Z)
are transported under energy-critical spatial rescaling
  V_a(r)=sqrt(a)*V(a*r), Z_a(r)=sqrt(a)*Z(a*r).

This is NOT an invented local cubic approximation: every original
logarithmic radial Hartree potential is rescaled using the genuine
radial change of variables. The full mixed density, pure radiation
potential, core potential and the cubic differences are retained.

The physically selected outer Kummer forcing is
  F0(r)=a²*Interaction(V_ell,c,Z_ell)(a*r).
The exact identity
  sqrt(a)*F0(r)=Interaction((V_ell,c)_a,(Z_ell)_a)(r)
moves the physical observation radius to a FIXED normalized annular
coordinate. Therefore a time derivative of the ACTUAL scaled
Hartree interaction can be produced at fixed r from the already
accepted genuine three-potential time derivative theorem; this
does not require differentiating the radial Riesz kernel at a
moving observation point. No blowup exponent is preselected.

The time-dependent rescaled real/complex field derivative estimates
and full four-piece weighted PDE residual remain separate obligations.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeCriticalScaledRealCore
    (a : ℝ) (V : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.sqrt a * V (a * r)

/-- The full original Riesz mixed quartic interaction obeys EXACT
critical scaling; there are no support or error assumptions. -/
theorem actual_Hartree_critical_scaled_full_mixed_interaction
    (a r : ℝ) (ha : 0 < a)
    (V : ℝ → ℝ) (Z : ℝ → ℂ) :
    actualOneLayerInteractionOnly
      (fun _ : ℝ => actualHartreeCriticalScaledRealCore a V)
      (fun _ : ℝ => rescalePhysicalRadiation a Z) 0 r =
      (((a ^ 2 * Real.sqrt a : ℝ) : ℂ)) *
        actualOneLayerInteractionOnly
          (fun _ : ℝ => V) (fun _ : ℝ => Z) 0 (a * r) := by
  let Vc : ℝ → ℂ := fun x => (V x : ℂ)
  let total : ℝ → ℂ := fun x => (V x : ℂ) + Z x
  let Va : ℝ → ℝ := actualHartreeCriticalScaledRealCore a V
  let Za : ℝ → ℂ := rescalePhysicalRadiation a Z
  have hVa : (fun x => (Va x : ℂ)) =
      rescalePhysicalRadiation a Vc := by
    funext x
    dsimp [Va, actualHartreeCriticalScaledRealCore, Vc,
      rescalePhysicalRadiation]
    push_cast
    ring
  have hTotal : (fun x => (Va x : ℂ) + Za x) =
      rescalePhysicalRadiation a total := by
    funext x
    dsimp [Va, Za, total, actualHartreeCriticalScaledRealCore,
      rescalePhysicalRadiation]
    push_cast
    ring
  have hNorm (w : ℂ) :
      ‖(Real.sqrt a : ℂ) * w‖ ^ 4 = a ^ 2 * ‖w‖ ^ 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg a), mul_pow]
    calc
      Real.sqrt a ^ 4 * ‖w‖ ^ 4 =
        (Real.sqrt a ^ 2) ^ 2 * ‖w‖ ^ 4 := by ring
      _ = a ^ 2 * ‖w‖ ^ 4 := by rw [Real.sq_sqrt ha.le]
  have hDensity : actualWholeRadiationMixedQuartic Va Za =
      (fun x => a ^ 2 *
        actualWholeRadiationMixedQuartic V Z (a * x)) := by
    funext x
    have hTotalAt : (Va x : ℂ) + Za x =
        (Real.sqrt a : ℂ) * ((V (a*x) : ℂ) + Z (a*x)) := by
      simpa only [hTotal, rescalePhysicalRadiation, total] using
        congrArg (fun f : ℝ → ℂ => f x) hTotal
    have hCoreAt : (Va x : ℂ) =
        (Real.sqrt a : ℂ) * (V (a*x) : ℂ) := by
      simpa only [hVa, rescalePhysicalRadiation, Vc] using
        congrArg (fun f : ℝ → ℂ => f x) hVa
    have hZAt : Za x =
        (Real.sqrt a : ℂ) * Z (a*x) := rfl
    dsimp [actualWholeRadiationMixedQuartic]
    rw [hTotalAt, hCoreAt, hZAt,
      hNorm, hNorm, hNorm]
    ring
  have hPm : radialHartreePotential
      (actualWholeRadiationMixedQuartic Va Za) r =
      a * radialHartreePotential
        (actualWholeRadiationMixedQuartic V Z) (a*r) := by
    rw [hDensity]
    exact actual_Hartree_radial_potential_scale_quartic_density
      a r ha (actualWholeRadiationMixedQuartic V Z)
  have hPz : radialHartreePotential
      (fun x => ‖Za x‖ ^ 4) r =
      a * radialHartreePotential (fun x => ‖Z x‖ ^ 4) (a*r) := by
    exact actual_Hartree_critical_radiation_Riesz_scaling a r ha Z
  have hPv : radialHartreePotential
      (fun x => ‖(Va x : ℂ)‖ ^ 4) r =
      a * radialHartreePotential (fun x => ‖(V x : ℂ)‖ ^ 4) (a*r) := by
    rw [show (fun x => ‖(Va x : ℂ)‖ ^ 4) =
        (fun x => ‖rescalePhysicalRadiation a Vc x‖ ^ 4) from by
          funext x
          rw [←hVa]]
    simpa only [Vc] using
      actual_Hartree_critical_radiation_Riesz_scaling a r ha Vc
  have hCt : actualWholeRadiationLocalCubic
      (fun x => (Va x : ℂ) + Za x) r =
      (((a * Real.sqrt a : ℝ) : ℂ)) *
        actualWholeRadiationLocalCubic total (a*r) := by
    rw [hTotal]
    exact actual_Hartree_critical_rescaled_local_cubic a r ha total
  have hCz : actualWholeRadiationLocalCubic Za r =
      (((a * Real.sqrt a : ℝ) : ℂ)) *
        actualWholeRadiationLocalCubic Z (a*r) := by
    exact actual_Hartree_critical_rescaled_local_cubic a r ha Z
  have hCv : actualWholeRadiationLocalCubic
      (fun x => (Va x : ℂ)) r =
      (((a * Real.sqrt a : ℝ) : ℂ)) *
        actualWholeRadiationLocalCubic Vc (a*r) := by
    rw [hVa]
    exact actual_Hartree_critical_rescaled_local_cubic a r ha Vc
  change actualOneLayerInteractionOnly
      (fun _ : ℝ => Va) (fun _ : ℝ => Za) 0 r =
      (((a ^ 2 * Real.sqrt a : ℝ) : ℂ)) *
        actualOneLayerInteractionOnly
          (fun _ : ℝ => V) (fun _ : ℝ => Z) 0 (a*r)
  unfold actualOneLayerInteractionOnly
  rw [hPm, hPz, hPv, hCt, hCz, hCv]
  push_cast
  ring

/-- Same ORIGINAL selected Kummer source, at FIXED normalized radius.
The observation-point motion has been transported entirely into the
physical energy-critical fields; no independent moving-observer
Riesz derivative is inserted. -/
theorem actual_Hartree_critical_scaled_selected_original_source
    (a ell c r : ℝ) (ha : 0 < a) (z : ℝ → ℂ) :
    ((Real.sqrt a : ℝ) : ℂ) *
      actualHartreeLaplacianScaledKummerSource a ell c z r =
    actualOneLayerInteractionOnly
      (fun _ : ℝ =>
        actualHartreeCriticalScaledRealCore a
          (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c))
      (fun _ : ℝ =>
        rescalePhysicalRadiation a (rescalePhysicalRadiation ell z)) 0 r := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  have hs := actual_Hartree_critical_scaled_full_mixed_interaction
    a r ha V Z
  unfold actualHartreeLaplacianScaledKummerSource
    actualHartreePhysicalSliceInteraction
  change ((Real.sqrt a : ℝ) : ℂ) *
      (((a ^ 2 : ℝ) : ℂ) *
        actualOneLayerInteractionOnly
          (fun _ : ℝ => V) (fun _ : ℝ => Z) 0 (a*r)) =
    actualOneLayerInteractionOnly
      (fun _ : ℝ => actualHartreeCriticalScaledRealCore a V)
      (fun _ : ℝ => rescalePhysicalRadiation a Z) 0 r
  rw [hs]
  push_cast
  ring

end HBL.TypeIIDynamicSelection
