import HBL.WeightedVolterraRadialForm
import HBL.WeightedVolterraAPlusCoercivity

/-!
Transfer the strict gap for the concrete Volterra operator onto the
actual reduced half-line radial-profile integral form.  All claims are
one-dimensional; identification with the three-dimensional physical
Hessian remains separate and unproved here.
-/

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- Exact squared norm of the smooth radial derivative coordinate. -/
theorem smoothRadialEnergy_coordinate_norm_sq
    (f : ℝ → ℝ)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure) :
    ‖smoothToRadialDotH1 f hfmem‖ ^ 2 =
      ∫ r : ℝ, (deriv (radialU f) r) ^ 2 ∂halfLineMeasure := by
  simpa only [real_inner_self_eq_norm_sq, pow_two] using
    smoothRadialEnergy_coordinate_pairing f f hfmem hfmem

/-- Quantitative coercivity of the actual half-line profile form
on the complement of its first two transferred sine modes. -/
theorem weightedVolterraAPlus_radial_profile_coercive
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hfirst : inner ℝ (weightedVolterraSineMode 0)
      (smoothToRadialDotH1 f hfmem) = 0)
    (hsecond : inner ℝ (weightedVolterraSineMode 1)
      (smoothToRadialDotH1 f hfmem) = 0) :
    (22 / 35 : ℝ) *
      (∫ r : ℝ, (deriv (radialU f) r) ^ 2 ∂halfLineMeasure) ≤
      (∫ r : ℝ, (deriv (radialU f) r) ^ 2 ∂halfLineMeasure) -
      (9 * (∫ r : ℝ, weightedGreenDecay r ^ 2 * radialU f r * radialU f r
        ∂halfLineMeasure) +
      ∫ p : ℝ × ℝ, hartreeKernel p.1 p.2 *
        (radialU f p.1 * radialU f p.2)
        ∂(halfLineMeasure.prod halfLineMeasure)) := by
  have hgap := weightedVolterraAPlus_tail_coercive
    (smoothToRadialDotH1 f hfmem) hfirst hsecond
  rw [weightedVolterraAPlus_radial_profile_pairing f f hf hf hfmem hfmem,
    smoothRadialEnergy_coordinate_norm_sq f hfmem] at hgap
  simpa only [pow_two] using hgap

end HBL.Modulation.Monopole
