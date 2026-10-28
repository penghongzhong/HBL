import HBL.WeightedSourceFredholmSolution
import HBL.WeightedPhaseSourceFredholmBridge
import HBL.AffineTailLemmaClosed

/-!
# Two actual Hartree threshold channels, without abstract solver packages

The physical H_plus and H_minus Birman-Schwinger operators have different
kernels, but both now admit verified normalized solves for arbitrary
compatible data in the original 3/2 < sigma < 2 source range.

This file combines the two explicit problems into a unique pair; it also
constructs both unique real affine threshold charges for arbitrary physical
sources. No theorem that an affine-corrected H_plus source lies in
L^(2,sigma), and no whole one-layer residual cancellation, is asserted.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Profile.ActualInner

open HBL.L2Kernel
open HBL.Modulation.AffineTail
open HBL.Modulation.Monopole

/-- Actual two-channel Hilbert correction space, with each component
normalized perpendicular to the corresponding *physical* Fredholm kernel. -/
abbrev InnerCorrections :=
  (1 - weightedBirmanSchwingerOperator).kerᗮ ×
  (1 - weightedPhaseBirman).kerᗮ

/-- All source spaces, operators and compatibility functionals in this
statement are the actual (non-abstract) Hartree ones. -/
theorem existsUnique_actual_twoChannel_compatible_solve
    (sigma : ℝ) (hsigmaLower : 3 / 2 < sigma) (hsigmaUpper : sigma < 2)
    (Fplus Fminus : ℝ → ℝ)
    (hFplus : InWeightedL2 sigma Fplus)
    (hFminus : InWeightedL2 sigma Fminus)
    (hchargePlus : channelPairing HartreeChannel.plus Fplus = 0)
    (hchargeMinus : channelPairing HartreeChannel.minus Fminus = 0) :
    ∃! x : InnerCorrections,
      (1 - weightedBirmanSchwingerOperator)
          (x.1 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator sigma (by linarith)
          (weightedSourceDataL2 sigma Fplus hFplus) ∧
      (1 - weightedPhaseBirman)
          (x.2 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator sigma (by linarith)
          (weightedSourceDataL2 sigma Fminus hFminus) := by
  have hsigma : 1 < sigma := by linarith
  obtain ⟨xp, hxp, hxpUniq⟩ :=
    existsUnique_weightedSourceFredholmSolution
      sigma hsigma Fplus hFplus hchargePlus
  obtain ⟨xm, hxm, hxmUniq⟩ :=
    existsUnique_phaseWeightedSourceFredholmSolve
      sigma hsigma Fminus hFminus hchargeMinus
  refine ⟨⟨xp, xm⟩, ?_, ?_⟩
  · constructor
    · exact hxp
    · exact hxm
  · intro x hx
    exact Prod.ext (hxpUniq x.1 hx.1) (hxmUniq x.2 hx.2)

/-- Both uniquely forced actual affine charges exist simultaneously,
for arbitrary physical L^(2,sigma) data. -/
theorem existsUnique_actual_twoChannel_affine_charges
    (sigma : ℝ) (hsigmaLower : 3 / 2 < sigma) (hsigmaUpper : sigma < 2)
    (Fplus Fminus : ℝ → ℝ)
    (hFplus : InWeightedL2 sigma Fplus)
    (hFminus : InWeightedL2 sigma Fminus) :
    ∃! a : ℝ × ℝ,
      AffineTailOrthogonal HartreeChannel.plus Fplus a.1 ∧
      AffineTailOrthogonal HartreeChannel.minus Fminus a.2 := by
  obtain ⟨ap, hap, hup⟩ :=
    (secondManuscriptAffineTailEnvironment_closed
      sigma hsigmaLower hsigmaUpper HartreeChannel.plus Fplus hFplus).1
  obtain ⟨am, ham, hum⟩ :=
    (secondManuscriptAffineTailEnvironment_closed
      sigma hsigmaLower hsigmaUpper HartreeChannel.minus Fminus hFminus).1
  refine ⟨⟨ap, am⟩, ⟨hap, ham⟩, ?_⟩
  intro a ha
  exact Prod.ext (hup a.1 ha.1) (hum a.2 ha.2)

#print axioms existsUnique_actual_twoChannel_compatible_solve
#print axioms existsUnique_actual_twoChannel_affine_charges

end HBL.Profile.ActualInner
