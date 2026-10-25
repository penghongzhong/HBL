import HBL.WeightedHartreePointwiseBound

/-!
Candidate: exact bilinear Hartree pairing in the original half-line profile
variables. NOT YET COMPILED.

Only a*q and a*v are required to belong to L2, where a(r)=(1+r^2)^(-1).
The unweighted profiles need not be in L2. Absolute product integrability
is proved from the actual product-L2 kernel and the product vector.
This is a reduced radial-kernel form identity, not a three-dimensional
angular-reduction theorem, a Sobolev completion, or a physical Hessian proof.
-/

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- Exact relation of the actual unweighted and weighted radial kernels. -/
theorem hartreeKernel_weighted_factorization (r s : ℝ) :
    hartreeKernel r s =
      weightedGreenDecay r * weightedHartreeKernel r s *
        weightedGreenDecay s := by
  have hw (x : ℝ) : weightedGreenDecay x = bubble x ^ 2 := by
    simp only [weightedGreenDecay, bubble_sq]
  rw [hw r, hw s]
  unfold hartreeKernel weightedHartreeKernel hartreeRadialLog
  ring

private theorem weightedHartree_profile_density_ae
    (q v : ℝ → ℝ)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure)
    (hv : MemLp (fun r => weightedGreenDecay r * v r) 2 halfLineMeasure) :
    (fun p : ℝ × ℝ =>
      inner ℝ (weightedHartreeKernelL2 p)
        (tensor
          (hv.toLp (fun r => weightedGreenDecay r * v r))
          (hq.toLp (fun r => weightedGreenDecay r * q r)) p)) =ᵐ[
        halfLineMeasure.prod halfLineMeasure]
      (fun p => hartreeKernel p.1 p.2 * (v p.1 * q p.2)) := by
  have hvprod :=
    (Measure.quasiMeasurePreserving_fst
      (μ := halfLineMeasure) (ν := halfLineMeasure)).ae hv.coeFn_toLp
  have hqprod :=
    (Measure.quasiMeasurePreserving_snd
      (μ := halfLineMeasure) (ν := halfLineMeasure)).ae hq.coeFn_toLp
  filter_upwards [weightedHartreeKernelL2_ae,
    tensor_ae (hv.toLp (fun r => weightedGreenDecay r * v r))
      (hq.toLp (fun r => weightedGreenDecay r * q r)),
    hvprod, hqprod] with p hK ht hvp hqp
  rw [hK, ht, Real.inner_apply, hvp, hqp,
    hartreeKernel_weighted_factorization]
  change weightedHartreeKernel p.1 p.2 *
      ((weightedGreenDecay p.1 * v p.1) *
        (weightedGreenDecay p.2 * q p.2)) =
    weightedGreenDecay p.1 * weightedHartreeKernel p.1 p.2 *
      weightedGreenDecay p.2 * (v p.1 * q p.2)
  ring

/-- Absolute integrability of the actual original-profile Hartree pairing.
No unweighted L2 membership of either profile is assumed. -/
theorem hartreeProfileForm_integrable
    (q v : ℝ → ℝ)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure)
    (hv : MemLp (fun r => weightedGreenDecay r * v r) 2 halfLineMeasure) :
    Integrable (fun p : ℝ × ℝ =>
      hartreeKernel p.1 p.2 * (v p.1 * q p.2))
      (halfLineMeasure.prod halfLineMeasure) := by
  exact (L2.integrable_inner weightedHartreeKernelL2
    (tensor (hv.toLp (fun r => weightedGreenDecay r * v r))
      (hq.toLp (fun r => weightedGreenDecay r * q r)))).congr
    (weightedHartree_profile_density_ae q v hq hv)

/-- The bounded weighted Hartree operator equals the actual nonlocal
double integral in the original half-line profile variables. -/
theorem weightedHartreeOperator_profile_pairing
    (q v : ℝ → ℝ)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure)
    (hv : MemLp (fun r => weightedGreenDecay r * v r) 2 halfLineMeasure) :
    inner ℝ
      (weightedHartreeOperator
        (hq.toLp (fun r => weightedGreenDecay r * q r)))
      (hv.toLp (fun r => weightedGreenDecay r * v r)) =
      ∫ p : ℝ × ℝ, hartreeKernel p.1 p.2 * (v p.1 * q p.2)
        ∂(halfLineMeasure.prod halfLineMeasure) := by
  change inner ℝ
      (operator weightedHartreeKernelL2
        (hq.toLp (fun r => weightedGreenDecay r * q r)))
      (hv.toLp (fun r => weightedGreenDecay r * v r)) = _
  rw [inner_operator, L2.inner_def]
  exact integral_congr_ae (weightedHartree_profile_density_ae q v hq hv)

/-- The local weighted profile pairing is the actual weighted integral. -/
theorem weightedProfile_inner
    (q v : ℝ → ℝ)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure)
    (hv : MemLp (fun r => weightedGreenDecay r * v r) 2 halfLineMeasure) :
    inner ℝ
      (hq.toLp (fun r => weightedGreenDecay r * q r))
      (hv.toLp (fun r => weightedGreenDecay r * v r)) =
      ∫ r : ℝ, weightedGreenDecay r ^ 2 * q r * v r
        ∂halfLineMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hq.coeFn_toLp, hv.coeFn_toLp] with r hqr hvr
  rw [hqr, hvr, Real.inner_apply]
  ring

/-- The actual potential operator has exactly the local and nonlocal
original-profile bilinear integrals, with the normalization retained. -/
theorem weightedPotentialOperator_profile_pairing
    (q v : ℝ → ℝ)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure)
    (hv : MemLp (fun r => weightedGreenDecay r * v r) 2 halfLineMeasure) :
    inner ℝ
      (weightedPotentialOperator
        (hq.toLp (fun r => weightedGreenDecay r * q r)))
      (hv.toLp (fun r => weightedGreenDecay r * v r)) =
      9 * (∫ r : ℝ, weightedGreenDecay r ^ 2 * q r * v r
        ∂halfLineMeasure) +
      ∫ p : ℝ × ℝ, hartreeKernel p.1 p.2 * (v p.1 * q p.2)
        ∂(halfLineMeasure.prod halfLineMeasure) := by
  unfold weightedPotentialOperator
  rw [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
    weightedProfile_inner q v hq hv,
    weightedHartreeOperator_profile_pairing q v hq hv]

end HBL.Modulation.Monopole
