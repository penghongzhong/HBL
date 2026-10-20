import HBL.WeightedVolterraOperator
import HBL.WeightedFreeGreenPointwise
import HBL.RadialEnergyCompletion
import HBL.RadialDotH1Model

/-!
The weighted Volterra bridge on the smooth radial energy-coordinate core.

For a C1 real profile `f` with `deriv (radialU f)` in half-line L2, the
actual bounded Volterra operator sends the coordinate represented by
`deriv (radialU f)` to the coordinate represented by
`weightedGreenDecay * radialU f`.

The proof only integrates the derivative over a finite interval, using
`radialU f 0 = 0` through the existing fundamental-theorem lemma.  It does
not assume that `radialU f` is itself in L2, compact support, a boundary
condition at infinity, a physical Sobolev identification, or a Hessian
identification.

This is an independent source candidate.  It has not been compiled.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The actual representative of the smooth energy coordinate has the
correct finite-interval primitive.  The restriction step is essential:
the coordinate representative agrees with the derivative only a.e. on
the positive half-line, not necessarily pointwise. -/
theorem smoothToRadialDotH1_integral_Ioo
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (r : ℝ) (hr : 0 ≤ r) :
    (∫ s in Ioo (0 : ℝ) r, smoothToRadialDotH1 f hmem s) =
      radialU f r := by
  have hae :
      (smoothToRadialDotH1 f hmem : ℝ → ℝ) =ᵐ[
        volume.restrict (Ioo (0 : ℝ) r)] deriv (radialU f) :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self
      (smoothToRadialDotH1_ae f hmem)
  calc
    (∫ s in Ioo (0 : ℝ) r, smoothToRadialDotH1 f hmem s) =
        ∫ s in Ioo (0 : ℝ) r, deriv (radialU f) s :=
      integral_congr_ae hae
    _ = ∫ s in Ioc (0 : ℝ) r, deriv (radialU f) s :=
      integral_Ioc_eq_integral_Ioo.symm
    _ = ∫ s in (0 : ℝ)..r, deriv (radialU f) s :=
      (intervalIntegral.integral_of_le hr).symm
    _ = radialU f r := radialU_integral_deriv f hf r

/-- On the C1 finite-energy coordinate core, the actual Volterra image
is represented a.e. by the weighted radial profile. -/
theorem weightedVolterraOperator_smoothToRadialDotH1_ae
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hmem : MemLp (deriv (radialU f)) 2 halfLineMeasure) :
    (weightedVolterraOperator (smoothToRadialDotH1 f hmem) : ℝ → ℝ) =ᵐ[
      halfLineMeasure] fun r => weightedGreenDecay r * radialU f r := by
  refine (weightedVolterraOperator_ae_pointwise
    (smoothToRadialDotH1 f hmem)).trans ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [smoothToRadialDotH1_integral_Ioo f hf hmem r
    (show 0 ≤ r from le_of_lt hr)]
  rfl

/-- Weighted radial-profile L2 membership is a consequence of the
bounded Volterra construction and the proved representative identity;
it is not an additional premise. -/
theorem weightedRadialU_memLp
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hmem : MemLp (deriv (radialU f)) 2 halfLineMeasure) :
    MemLp (fun r => weightedGreenDecay r * radialU f r) 2
      halfLineMeasure := by
  exact MemLp.ae_eq
    (weightedVolterraOperator_smoothToRadialDotH1_ae f hf hmem)
    (Lp.memLp (weightedVolterraOperator (smoothToRadialDotH1 f hmem)))

/-- Exact equality of the Volterra image and the L2 class of the
weighted profile, with membership supplied by the preceding theorem. -/
theorem weightedVolterraOperator_smoothToRadialDotH1_eq
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hmem : MemLp (deriv (radialU f)) 2 halfLineMeasure) :
    weightedVolterraOperator (smoothToRadialDotH1 f hmem) =
      (weightedRadialU_memLp f hf hmem).toLp
        (fun r => weightedGreenDecay r * radialU f r) := by
  apply Lp.ext
  exact (weightedVolterraOperator_smoothToRadialDotH1_ae f hf hmem).trans
    (weightedRadialU_memLp f hf hmem).coeFn_toLp.symm

end HBL.Modulation.Monopole
