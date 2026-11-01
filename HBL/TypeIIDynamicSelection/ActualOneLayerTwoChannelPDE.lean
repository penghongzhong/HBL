import HBL.TypeIIDynamicSelection.ActualOneLayerPDEResidual
import HBL.ActualInnerAffinelyCorrected
import Mathlib.Tactic

/-!
# Both real H+ and phase H- sources from ONE genuine Hartree PDE residual

The real and imaginary sources below are NOT independent inputs.
They are the two physical channel components of the identical complete
renormalized 3D radial Hartree residual, in the real-core modulation gauge.

The exact source theorem keeps the time derivative, Laplacian, dilation,
phase, self-radiation Riesz term, the COMPLETE quartic mixed Riesz term,
and the changed local cubic term. Its two Fredholm affine charges
therefore come from the SAME physical residual, not from a surrogate
real quartic density used in both channels.

Weighted source membership is a visible remaining analytic obligation:
it is not manufactured by this source-identity proof. Kummer/remote
matching and all positive generated orders are still needed for
original manuscript one-layer environment 2.12.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Modulation.AffineTail
open HBL.Profile.ActualInner
open HBL.Modulation.Monopole

/-- The single physical renormalized Hartree source after inserting
the real core and the entire complex radiation. -/
def actualOneLayerCommonPDEResidual
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) : ℂ :=
  complexRadialRenormalizedResidual
    (fun t x => (V t x : ℂ) + Z t x) b omega s r -
  complexRadialRenormalizedResidual
    (fun t x => (V t x : ℂ)) b omega s r

/-- H+ source is the real part of the same PDE residual. -/
def actualOneLayerPlusPDE
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s : ℝ) : ℝ → ℝ :=
  fun r => (actualOneLayerCommonPDEResidual V Z b omega s r).re

/-- H- source is the imaginary part of that same PDE residual. -/
def actualOneLayerMinusPDE
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s : ℝ) : ℝ → ℝ :=
  fun r => (actualOneLayerCommonPDEResidual V Z b omega s r).im

/-- Exact complete source on the right-hand side of the true
Hartree PDE residual identity, not a freely assigned regional forcing. -/
def actualOneLayerFullHartreeForcing
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) : ℂ :=
  Complex.I * deriv (fun t : ℝ => Z t r) s +
    complexRadialLaplacian (Z s) r +
    Complex.I * (b : ℂ) * complexRadialDilation (Z s) r +
    (omega : ℂ) * Z s r +
    ((radialHartreePotential (fun rho => ‖Z s rho‖ ^ 4) r +
      radialHartreePotential
        (actualWholeRadiationMixedQuartic (V s) (Z s)) r : ℝ) : ℂ) *
      actualWholeRadiationLocalCubic
        (fun rho => (V s rho : ℂ) + Z s rho) r +
    (radialHartreePotential
      (fun rho => ‖(V s rho : ℂ)‖ ^ 4) r : ℂ) *
      (actualWholeRadiationLocalCubic
          (fun rho => (V s rho : ℂ) + Z s rho) r -
        actualWholeRadiationLocalCubic
          (fun rho => (V s rho : ℂ)) r)

/-- Both physical channel sources are obtained SIMULTANEOUSLY
from the same complete time-dependent Hartree PDE identity. In
particular, neither channel is replaced by a real quartic density. -/
theorem actual_one_layer_common_PDE_both_channels_exact
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
        ‖Z s rho‖ ^ 4) (Ioi (0 : ℝ))) :
    actualOneLayerPlusPDE V Z b omega s r =
      (actualOneLayerFullHartreeForcing V Z b omega s r).re ∧
    actualOneLayerMinusPDE V Z b omega s r =
      (actualOneLayerFullHartreeForcing V Z b omega s r).im := by
  have h := actual_one_layer_full_renormalized_Hartree_PDE_source
    V Z b omega s r hVTime hZTime hVSpace hZSpace
      hVSecond hZSecond hFullRow hCoreRow hRadiationRow
  exact ⟨congrArg Complex.re h, congrArg Complex.im h⟩

/-- Unique real affine threshold-charge PAIR of the actual PDE
channel sources, provided those SAME sources satisfy the physical
weighted Fredholm integrability conditions. This specializes the
manuscript's already verified independent two-channel inverse. -/
theorem actual_one_layer_common_PDE_unique_affine_charges
    (sigma : ℝ) (hSigma : 3 / 2 < sigma)
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s : ℝ)
    (hPlus : InWeightedL2 sigma (actualOneLayerPlusPDE V Z b omega s))
    (hMinus : InWeightedL2 sigma (actualOneLayerMinusPDE V Z b omega s)) :
    ∃! charges : ℝ × ℝ,
      AffineTailOrthogonal HartreeChannel.plus
        (actualOneLayerPlusPDE V Z b omega s) charges.1 ∧
      AffineTailOrthogonal HartreeChannel.minus
        (actualOneLayerMinusPDE V Z b omega s) charges.2 := by
  let Fp := actualOneLayerPlusPDE V Z b omega s
  let Fm := actualOneLayerMinusPDE V Z b omega s
  have hs : 1 / 2 < sigma := by linarith
  refine ⟨(actualPlusCharge Fp, actualMinusCharge Fm), ?_, ?_⟩
  · exact ⟨actualPlusCharge_orthogonal sigma hs Fp hPlus,
      actualMinusCharge_orthogonal sigma hs Fm hMinus⟩
  · intro charges hcharges
    exact Prod.ext
      (actualPlusCharge_unique sigma hs Fp hPlus charges.1 hcharges.1)
      (actualMinusCharge_unique sigma hs Fm hMinus charges.2 hcharges.2)

/-- The same physical two projected PDE sources select a unique
pair of affine-corrected normalized H+/H- Fredholm solutions.
No physical weighted source bounds are silently assumed here. -/
theorem actual_one_layer_common_PDE_unique_inner_solutions
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s : ℝ)
    (hPlus : InWeightedL2 sigma (actualOneLayerPlusPDE V Z b omega s))
    (hMinus : InWeightedL2 sigma (actualOneLayerMinusPDE V Z b omega s)) :
    ∃! x : InnerCorrections,
      (1 - weightedBirmanSchwingerOperator)
          (x.1 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator sigma (by linarith)
          (weightedSourceDataL2 sigma
            (correctedPlusSource (actualOneLayerPlusPDE V Z b omega s))
            (correctedPlusSource_memWeightedL2 sigma hUpper.le
              (actualOneLayerPlusPDE V Z b omega s) hPlus)) ∧
      (1 - weightedPhaseBirman)
          (x.2 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator sigma (by linarith)
          (weightedSourceDataL2 sigma
            (correctedMinusSource (actualOneLayerMinusPDE V Z b omega s))
            (correctedMinusSource_memWeightedL2 sigma hUpper.le
              (actualOneLayerMinusPDE V Z b omega s) hMinus)) := by
  exact existsUnique_actualInner_affinelyCorrected sigma hLower hUpper
    (actualOneLayerPlusPDE V Z b omega s)
    (actualOneLayerMinusPDE V Z b omega s) hPlus hMinus

end HBL.TypeIIDynamicSelection
