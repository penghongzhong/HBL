import HBL.InnerReconstruction.ActualTwoChannelReconstruction
import HBL.InnerReconstruction.AffineRestorationProperties
import HBL.InnerReconstruction.AffineRestorationPlusEquation
import HBL.InnerReconstruction.AffineRestorationPhaseEquation

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

/-- Original-source classical solutions with the forced physical affine slopes,
origin boundary values, weighted output, finite affine tails, and the actual
Hilbert kernel-complement normalization. No manuscript nonlinear closure is claimed. -/
theorem exists_actualInner_classical_affine
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (Fplus Fminus : ℝ → ℝ)
    (hp : InWeightedL2 sigma Fplus) (hm : InWeightedL2 sigma Fminus)
    (hcp : Continuous Fplus) (hcm : Continuous Fminus) :
    ∃ x : InnerCorrections, ∃ up um : ℝ → ℝ,
    ((x.1 : RealL2 halfLineMeasure) : ℝ → ℝ) =ᵐ[halfLineMeasure]
      (fun r => weightedGreenDecay r * (up r - actualPlusCharge Fplus * model r)) ∧
    ((x.2 : RealL2 halfLineMeasure) : ℝ → ℝ) =ᵐ[halfLineMeasure]
      (fun r => weightedGreenDecay r * (um r - actualMinusCharge Fminus * model r)) ∧
    InnerAffineProperties up (actualPlusCharge Fplus) ∧
    InnerAffineProperties um (actualMinusCharge Fminus) ∧
    (∀ r : ℝ, 0 < r →
      DifferentiableAt ℝ up r ∧ DifferentiableAt ℝ (deriv up) r ∧
      DifferentiableAt ℝ um r ∧ DifferentiableAt ℝ (deriv um) r ∧
      hPlusApply up r = Fplus r ∧ hMinusApply um r = Fminus r) := by
  obtain ⟨x, hx⟩ := exists_actualInner_reconstructed sigma hLower hUpper Fplus Fminus hp hm
  dsimp only at hx
  rcases hx with ⟨hxp, hxm, hpp, hmp, hpc, hmc⟩
  let qp := innerGreenRepresentative (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
    (correctedPlusSource Fplus)
  let qm := innerGreenRepresentative ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
    (correctedMinusSource Fminus)
  have hpd : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ qp r :=
    fun r hr => (hpc hcp r hr).1.differentiableAt
  have hpdd : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv qp) r :=
    fun r hr => (hpc hcp r hr).2.1.differentiableAt
  have hmd : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ qm r :=
    fun r hr => (hmc hcm r hr).1.differentiableAt
  have hmdd : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv qm) r :=
    fun r hr => (hmc hcm r hr).2.1.differentiableAt
  have hmem : MemLp (fun r => weightedGreenDecay r * qp r) 2 halfLineMeasure :=
    (Lp.memLp (x.1 : RealL2 halfLineMeasure)).ae_eq hxp
  refine ⟨x, affineRestore qp (actualPlusCharge Fplus),
    affineRestore qm (actualMinusCharge Fminus), ?_, ?_,
    affineRestore_properties qp _ hpp, affineRestore_properties qm _ hmp, ?_⟩
  · simpa only [affineRestore, add_sub_cancel_right] using hxp
  · simpa only [affineRestore, add_sub_cancel_right] using hxm
  · intro r hr
    have hmodel := (contDiff_infty_iff_deriv.mp model_contDiff_infty).1 r
    refine ⟨(hpd r hr).add (hmodel.const_mul _),
      (affineRestore_second_hasDerivAt qp _ hpd hpdd hr).differentiableAt,
      (hmd r hr).add (hmodel.const_mul _),
      (affineRestore_second_hasDerivAt qm _ hmd hmdd hr).differentiableAt, ?_, ?_⟩
    · rw [affineRestore_hPlus qp _ hpd hpdd hmem hr, (hpc hcp r hr).2.2]
      change Fplus r - actualPlusCharge Fplus * hPlusApply model r +
        actualPlusCharge Fplus * hPlusApply model r = Fplus r
      ring
    · rw [affineRestore_hMinus qm _ hmd hmdd hr, (hmc hcm r hr).2.2]
      change Fminus r - actualMinusCharge Fminus * hMinusApply model r +
        actualMinusCharge Fminus * hMinusApply model r = Fminus r
      ring
end HBL.Modulation.Monopole
