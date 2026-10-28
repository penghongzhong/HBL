import HBL.InnerReconstruction.RepresentativeProperties
import HBL.InnerReconstruction.PlusClassicalEquation
import HBL.InnerReconstruction.PhaseClassicalEquation
import HBL.InnerReconstruction.CorrectedPlusContinuous
import HBL.InnerReconstruction.CorrectedPhaseContinuous
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

open HBL.Profile.ActualInner

/-- Actual normalized Hilbert solutions have continuous weighted representatives with
finite constant tails; continuous input sources give the actual classical equations. -/
theorem exists_actualInner_reconstructed
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (Fplus Fminus : ℝ → ℝ)
    (hp : InWeightedL2 sigma Fplus) (hm : InWeightedL2 sigma Fminus) :
    ∃ x : InnerCorrections,
    let qp := innerGreenRepresentative (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
      (correctedPlusSource Fplus)
    let qm := innerGreenRepresentative ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
      (correctedMinusSource Fminus)
    ((x.1 : RealL2 halfLineMeasure) : ℝ → ℝ) =ᵐ[halfLineMeasure]
      (fun r => weightedGreenDecay r * qp r) ∧
    ((x.2 : RealL2 halfLineMeasure) : ℝ → ℝ) =ᵐ[halfLineMeasure]
      (fun r => weightedGreenDecay r * qm r) ∧
    InnerRemainderProperties qp ∧ InnerRemainderProperties qm ∧
    (Continuous Fplus → ∀ r : ℝ, 0 < r →
      HasDerivAt qp (halfLineGreenTail (reconstructedPlusSource qp (correctedPlusSource Fplus)) r) r ∧
      HasDerivAt (deriv qp) (-reconstructedPlusSource qp (correctedPlusSource Fplus) r) r ∧
      hPlusApply qp r = correctedPlusSource Fplus r) ∧
    (Continuous Fminus → ∀ r : ℝ, 0 < r →
      HasDerivAt qm (halfLineGreenTail (reconstructedPhaseSource qm (correctedMinusSource Fminus)) r) r ∧
      HasDerivAt (deriv qm) (-reconstructedPhaseSource qm (correctedMinusSource Fminus) r) r ∧
      hMinusApply qm r = correctedMinusSource Fminus r) := by
  obtain ⟨x, hx, _⟩ := existsUnique_actualInner_affinelyCorrected sigma hLower hUpper Fplus Fminus hp hm
  have hp0 := correctedPlusSource_memWeightedL2 sigma hUpper.le Fplus hp
  have hm0 := correctedMinusSource_memWeightedL2 sigma hUpper.le Fminus hm
  refine ⟨x, ?_⟩
  dsimp only
  refine ⟨plus_innerGreenRepresentative_ae _ sigma (by linarith) _ hp0 hx.1,
    phase_innerGreenRepresentative_ae _ sigma (by linarith) _ hm0 hx.2,
    innerGreenRepresentative_properties _ sigma hLower _ hp0,
    innerGreenRepresentative_properties _ sigma hLower _ hm0, ?_, ?_⟩
  · intro hc
    exact plus_innerGreenRepresentative_classical _ sigma (by linarith) _ hp0
      (correctedPlusSource_continuous Fplus hc) hx.1
  · intro hc
    exact phase_innerGreenRepresentative_classical _ sigma (by linarith) _ hm0
      (correctedMinusSource_continuous Fminus hc) hx.2
end HBL.Modulation.Monopole
