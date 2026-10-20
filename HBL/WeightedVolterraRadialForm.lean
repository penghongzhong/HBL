import HBL.WeightedVolterraProfileBridge
import HBL.WeightedHartreeProfileForm
import HBL.WeightedVolterraAPlusKernel

/-!
Candidate: exact original-profile form of the actual Volterra-channel A.
NOT YET COMPILED.

The first term is the derivative-coordinate pairing of (r*f)' and (r*g)'.
The local and nonlocal potential terms use the original profiles r*f, r*g.
This is a genuine integral identity, not a renamed operator definition.
It does not yet replace the derivative-coordinate term by the physical
three-dimensional radial gradient term, or identify a physical Hessian.
-/

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The coordinate pairing is the actual derivative-product integral. -/
theorem smoothRadialEnergy_coordinate_pairing
    (f g : ℝ → ℝ)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hgmem : MemLp (deriv (radialU g)) 2 halfLineMeasure) :
    inner ℝ (smoothToRadialDotH1 f hfmem) (smoothToRadialDotH1 g hgmem) =
      ∫ r : ℝ, deriv (radialU f) r * deriv (radialU g) r
        ∂halfLineMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothToRadialDotH1_ae f hfmem,
    smoothToRadialDotH1_ae g hgmem] with r hfr hgr
  rw [hfr, hgr, Real.inner_apply]

/-- Actual potential pairing on smooth derivative coordinates, with the
weighted profile membership derived from V rather than assumed. -/
theorem weightedVolterraPotential_radial_profile_pairing
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hgmem : MemLp (deriv (radialU g)) 2 halfLineMeasure) :
    inner ℝ
      (weightedPotentialOperator
        (weightedVolterraOperator (smoothToRadialDotH1 f hfmem)))
      (weightedVolterraOperator (smoothToRadialDotH1 g hgmem)) =
      9 * (∫ r : ℝ, weightedGreenDecay r ^ 2 * radialU f r * radialU g r
        ∂halfLineMeasure) +
      ∫ p : ℝ × ℝ, hartreeKernel p.1 p.2 *
        (radialU g p.1 * radialU f p.2)
        ∂(halfLineMeasure.prod halfLineMeasure) := by
  rw [weightedVolterraOperator_smoothToRadialDotH1_eq f hf hfmem,
    weightedVolterraOperator_smoothToRadialDotH1_eq g hg hgmem]
  exact weightedPotentialOperator_profile_pairing (radialU f) (radialU g)
    (weightedRadialU_memLp f hf hfmem) (weightedRadialU_memLp g hg hgmem)

/-- Exact reduced integral form of the actual A on smooth profiles.
The unweighted profiles are not required to be L2 and no endpoint value
at infinity is silently inserted as a hypothesis. -/
theorem weightedVolterraAPlus_radial_profile_pairing
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hgmem : MemLp (deriv (radialU g)) 2 halfLineMeasure) :
    inner ℝ (weightedVolterraAPlus (smoothToRadialDotH1 f hfmem))
      (smoothToRadialDotH1 g hgmem) =
      (∫ r : ℝ, deriv (radialU f) r * deriv (radialU g) r
        ∂halfLineMeasure) -
      (9 * (∫ r : ℝ, weightedGreenDecay r ^ 2 * radialU f r * radialU g r
        ∂halfLineMeasure) +
      ∫ p : ℝ × ℝ, hartreeKernel p.1 p.2 *
        (radialU g p.1 * radialU f p.2)
        ∂(halfLineMeasure.prod halfLineMeasure)) := by
  change inner ℝ
    (smoothToRadialDotH1 f hfmem -
      ContinuousLinearMap.adjoint weightedVolterraOperator
        (weightedPotentialOperator
          (weightedVolterraOperator (smoothToRadialDotH1 f hfmem))))
    (smoothToRadialDotH1 g hgmem) = _
  rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    smoothRadialEnergy_coordinate_pairing f g hfmem hgmem,
    weightedVolterraPotential_radial_profile_pairing f g hf hg hfmem hgmem]

end HBL.Modulation.Monopole
