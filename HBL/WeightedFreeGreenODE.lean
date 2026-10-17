import HBL.WeightedFreeGreenPointwise
import HBL.WeightedScaleGreen
import Mathlib.Analysis.ODE.ExistUnique

/-!
ODE regularity and the distinguished eigenspace of the weighted free
half-line Green operator.

The weak Hilbert--Schmidt operator constructed earlier has the canonical
representative

  `a(r) * ∫ min r rho * a(rho) f(rho) d rho`,  `a(r) = (1+r^2)^(-1)`.

This file differentiates the unweighted primitive without differentiating
an L2 representative.  At a nonzero eigenvalue the integral equation first
upgrades the source to a continuous function; the usual two derivatives
then follow from the fundamental theorem of calculus.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- Dirichlet zero-slope Green primitive of a scalar source on `(0,∞)`. -/
def halfLineMinGreen (h : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ rho in Ioi (0 : ℝ), min r rho * h rho

/-- Outgoing derivative associated with the half-line Green primitive. -/
def halfLineGreenTail (h : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ rho in Ioi r, h rho

theorem halfLineMinGreen_split
    {h : ℝ → ℝ} (hcont : Continuous h)
    (hh : IntegrableOn h (Ioi (0 : ℝ)))
    {r : ℝ} (hr : 0 < r) :
    halfLineMinGreen h r =
      (∫ rho in (0 : ℝ)..r, rho * h rho) +
        r * halfLineGreenTail h r := by
  have hleftInt : IntegrableOn
      (fun rho : ℝ => min r rho * h rho) (Ioc (0 : ℝ) r) := by
    exact ((continuous_const.min continuous_id).mul hcont).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have htailInt : IntegrableOn
      (fun rho : ℝ => min r rho * h rho) (Ioi r) := by
    have hhr : IntegrableOn h (Ioi r) :=
      hh.mono_set (Ioi_subset_Ioi hr.le)
    refine (hhr.const_mul r).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hρ
    change r * h rho = min r rho * h rho
    rw [min_eq_left hρ.le]
  unfold halfLineMinGreen
  rw [← Ioc_union_Ioi_eq_Ioi hr.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hleftInt htailInt]
  congr 1
  · rw [intervalIntegral.integral_of_le hr.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro rho hρ
    change min r rho * h rho = rho * h rho
    rw [min_eq_right hρ.2]
  · unfold halfLineGreenTail
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro rho hρ
    change min r rho * h rho = r * h rho
    rw [min_eq_left hρ.le]

theorem halfLineGreenTail_eq_total_sub_interval
    {h : ℝ → ℝ} (hcont : Continuous h)
    (hh : IntegrableOn h (Ioi (0 : ℝ)))
    {r : ℝ} (hr : 0 < r) :
    halfLineGreenTail h r =
      (∫ rho in Ioi (0 : ℝ), h rho) - ∫ rho in (0 : ℝ)..r, h rho := by
  have hleft : IntegrableOn h (Ioc (0 : ℝ) r) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have htail : IntegrableOn h (Ioi r) :=
    hh.mono_set (Ioi_subset_Ioi hr.le)
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi hleft htail
  rw [Ioc_union_Ioi_eq_Ioi hr.le] at hsplit
  have hleft_eq : (∫ rho in Ioc (0 : ℝ) r, h rho) =
      ∫ rho in (0 : ℝ)..r, h rho := by
    rw [intervalIntegral.integral_of_le hr.le]
  rw [hleft_eq] at hsplit
  unfold halfLineGreenTail
  linarith

@[simp]
theorem halfLineMinGreen_zero (h : ℝ → ℝ) :
    halfLineMinGreen h 0 = 0 := by
  unfold halfLineMinGreen
  calc
    (∫ rho in Ioi (0 : ℝ), min 0 rho * h rho) =
        ∫ _rho in Ioi (0 : ℝ), (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hρ
      rw [min_eq_left hρ.le]
      simp
    _ = 0 := by simp

/-- Right derivative at the Dirichlet endpoint. -/
theorem halfLineMinGreen_hasDerivWithinAt_zero
    {h : ℝ → ℝ} (hcont : Continuous h)
    (hh : IntegrableOn h (Ioi (0 : ℝ))) :
    HasDerivWithinAt (halfLineMinGreen h) (halfLineGreenTail h 0)
      (Ici 0) 0 := by
  let C : ℝ := ∫ rho in Ioi (0 : ℝ), h rho
  let A : ℝ → ℝ := fun x => ∫ rho in (0 : ℝ)..x, rho * h rho
  let B : ℝ → ℝ := fun x => ∫ rho in (0 : ℝ)..x, h rho
  have hA : HasDerivAt A 0 0 := by
    unfold A
    convert intervalIntegral.integral_hasDerivAt_right
      ((continuous_id.mul hcont).intervalIntegrable 0 0)
      (continuous_id.mul hcont).aestronglyMeasurable.stronglyMeasurableAtFilter
      (continuous_id.mul hcont).continuousAt using 1
    · funext x
      apply intervalIntegral.integral_congr
      intro rho _
      simp only [Pi.mul_apply, id_eq]
    · simp
  have hB : HasDerivAt B (h 0) 0 := by
    unfold B
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 0)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hmodel : HasDerivAt (fun x : ℝ => A x + x * (C - B x)) C 0 := by
    convert hA.add ((hasDerivAt_id 0).mul
      ((hasDerivAt_const 0 C).sub hB)) using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
    · simp [B]
  have hcongr : ∀ x ∈ Ici (0 : ℝ),
      halfLineMinGreen h x = A x + x * (C - B x) := by
    intro x hx
    have hx' : 0 ≤ x := hx
    rcases hx'.eq_or_lt with rfl | hx
    · simp [A, B]
    · rw [halfLineMinGreen_split hcont hh hx,
        halfLineGreenTail_eq_total_sub_interval hcont hh hx]
  unfold halfLineGreenTail
  change HasDerivWithinAt (halfLineMinGreen h) C (Ici 0) 0
  exact hmodel.hasDerivWithinAt.congr hcongr (hcongr 0 (by simp))

/-- Right derivative of the outgoing tail at the endpoint. -/
theorem halfLineGreenTail_hasDerivWithinAt_zero
    {h : ℝ → ℝ} (hcont : Continuous h)
    (hh : IntegrableOn h (Ioi (0 : ℝ))) :
    HasDerivWithinAt (halfLineGreenTail h) (-h 0) (Ici 0) 0 := by
  let C : ℝ := ∫ rho in Ioi (0 : ℝ), h rho
  let B : ℝ → ℝ := fun x => ∫ rho in (0 : ℝ)..x, h rho
  have hB : HasDerivAt B (h 0) 0 := by
    unfold B
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 0)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hmodel : HasDerivAt (fun x : ℝ => C - B x) (-h 0) 0 := by
    convert (hasDerivAt_const 0 C).sub hB using 1 <;> ring
  have hcongr : ∀ x ∈ Ici (0 : ℝ),
      halfLineGreenTail h x = C - B x := by
    intro x hx
    have hx' : 0 ≤ x := hx
    rcases hx'.eq_or_lt with rfl | hx
    · simp [halfLineGreenTail, C, B]
    · rw [halfLineGreenTail_eq_total_sub_interval hcont hh hx]
  exact hmodel.hasDerivWithinAt.congr hcongr (hcongr 0 (by simp))

/-- The first derivative of the minimum-kernel primitive is its outgoing
tail integral. -/
theorem halfLineMinGreen_hasDerivAt
    {h : ℝ → ℝ} (hcont : Continuous h)
    (hh : IntegrableOn h (Ioi (0 : ℝ)))
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (halfLineMinGreen h) (halfLineGreenTail h r) r := by
  let C : ℝ := ∫ rho in Ioi (0 : ℝ), h rho
  let A : ℝ → ℝ := fun x => ∫ rho in (0 : ℝ)..x, rho * h rho
  let B : ℝ → ℝ := fun x => ∫ rho in (0 : ℝ)..x, h rho
  have hA : HasDerivAt A (r * h r) r := by
    unfold A
    exact intervalIntegral.integral_hasDerivAt_right
      ((continuous_id.mul hcont).intervalIntegrable 0 r)
      (continuous_id.mul hcont).aestronglyMeasurable.stronglyMeasurableAtFilter
      (continuous_id.mul hcont).continuousAt
  have hB : HasDerivAt B (h r) r := by
    unfold B
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 r)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hmodel : HasDerivAt (fun x : ℝ => A x + x * (C - B x))
      (C - B r) r := by
    convert hA.add ((hasDerivAt_id r).mul
      ((hasDerivAt_const r C).sub hB)) using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
    · simp only [Pi.sub_apply, id_eq]
      ring
  rw [halfLineGreenTail_eq_total_sub_interval hcont hh hr]
  change HasDerivAt (halfLineMinGreen h) (C - B r) r
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with x hx
  rw [halfLineMinGreen_split hcont hh hx,
    halfLineGreenTail_eq_total_sub_interval hcont hh hx]

/-- The outgoing tail differentiates to minus the continuous source. -/
theorem halfLineGreenTail_hasDerivAt
    {h : ℝ → ℝ} (hcont : Continuous h)
    (hh : IntegrableOn h (Ioi (0 : ℝ)))
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (halfLineGreenTail h) (-h r) r := by
  let C : ℝ := ∫ rho in Ioi (0 : ℝ), h rho
  let B : ℝ → ℝ := fun x => ∫ rho in (0 : ℝ)..x, h rho
  have hB : HasDerivAt B (h r) r := by
    unfold B
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 r)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hmodel : HasDerivAt (fun x : ℝ => C - B x) (-h r) r := by
    convert (hasDerivAt_const r C).sub hB using 1 <;> ring
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with x hx
  rw [halfLineGreenTail_eq_total_sub_interval hcont hh hx]

theorem halfLineMinGreen_second_hasDerivAt
    {h : ℝ → ℝ} (hcont : Continuous h)
    (hh : IntegrableOn h (Ioi (0 : ℝ)))
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (halfLineMinGreen h)) (-h r) r := by
  apply (halfLineGreenTail_hasDerivAt hcont hh hr).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with x hx
  exact (halfLineMinGreen_hasDerivAt hcont hh hx).deriv

/-- Continuous source produced by a nonzero Green eigenpair. -/
def weightedGreenEigenSource
    (mu : ℝ) (f : RealL2 halfLineMeasure) (r : ℝ) : ℝ :=
  mu⁻¹ * weightedGreenDecay r ^ 2 * weightedGreenPrimitive f r

theorem weightedGreenEigenSource_continuous
    (mu : ℝ) (f : RealL2 halfLineMeasure) :
    Continuous (weightedGreenEigenSource mu f) := by
  unfold weightedGreenEigenSource
  exact (continuous_const.mul (weightedGreenDecay_continuous.pow 2)).mul
    (weightedGreenPrimitive_continuous f)

theorem weightedGreen_eigen_source_ae
    {mu : ℝ} (hmu : mu ≠ 0) (f : RealL2 halfLineMeasure)
    (heig : weightedFreeGreenOperator f = mu • f) :
    (fun r : ℝ => weightedGreenDecay r * f r) =ᵐ[halfLineMeasure]
      weightedGreenEigenSource mu f := by
  have hpoint := weightedFreeGreenOperator_ae_pointwise f
  rw [heig] at hpoint
  filter_upwards [hpoint, Lp.coeFn_smul mu f] with r hpoint hsmul
  rw [hsmul] at hpoint
  simp only [Pi.smul_apply, smul_eq_mul] at hpoint
  unfold weightedFreeGreenPointwise at hpoint
  unfold weightedGreenEigenSource
  have hm : mu⁻¹ * mu = 1 := inv_mul_cancel₀ hmu
  calc
    weightedGreenDecay r * f r =
        mu⁻¹ * weightedGreenDecay r * (mu * f r) := by
      field_simp [hmu]
    _ = mu⁻¹ * weightedGreenDecay r *
        (weightedGreenDecay r * weightedGreenPrimitive f r) := by rw [hpoint]
    _ = mu⁻¹ * weightedGreenDecay r ^ 2 *
        weightedGreenPrimitive f r := by ring

theorem weightedGreenEigenSource_integrableOn
    {mu : ℝ} (hmu : mu ≠ 0) (f : RealL2 halfLineMeasure)
    (heig : weightedFreeGreenOperator f = mu • f) :
    IntegrableOn (weightedGreenEigenSource mu f) (Ioi 0) := by
  have hsrc := weightedGreen_source_integrable f
  exact hsrc.congr (weightedGreen_eigen_source_ae hmu f heig)

theorem weightedGreenPrimitive_eq_eigen_minGreen
    {mu : ℝ} (hmu : mu ≠ 0) (f : RealL2 halfLineMeasure)
    (heig : weightedFreeGreenOperator f = mu • f) :
    weightedGreenPrimitive f = halfLineMinGreen (weightedGreenEigenSource mu f) := by
  funext r
  unfold weightedGreenPrimitive halfLineMinGreen halfLineMeasure
  apply integral_congr_ae
  filter_upwards [weightedGreen_eigen_source_ae hmu f heig] with rho hρ
  rw [hρ]

/-- A nonzero Green eigenpair has a classical second-order representative
on the open half-line. -/
theorem weightedGreenPrimitive_eigen_second
    {mu : ℝ} (hmu : mu ≠ 0) (f : RealL2 halfLineMeasure)
    (heig : weightedFreeGreenOperator f = mu • f)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (weightedGreenPrimitive f))
      (-weightedGreenEigenSource mu f r) r := by
  rw [weightedGreenPrimitive_eq_eigen_minGreen hmu f heig]
  exact halfLineMinGreen_second_hasDerivAt
    (weightedGreenEigenSource_continuous mu f)
    (weightedGreenEigenSource_integrableOn hmu f heig) hr

theorem weightedGreenEigenSource_one_fifteen
    (f : RealL2 halfLineMeasure) (r : ℝ) :
    weightedGreenEigenSource (1 / 15 : ℝ) f r =
      15 * weightedGreenDecay r ^ 2 * weightedGreenPrimitive f r := by
  unfold weightedGreenEigenSource
  norm_num

/-- First-order system corresponding to
`-q'' = 15 (1+r^2)^(-2) q`. -/
def scaleGreenODEField (r : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, -15 * weightedGreenDecay r ^ 2 * z.1)

theorem weightedGreenDecay_le_one (r : ℝ) :
    weightedGreenDecay r ≤ 1 := by
  unfold weightedGreenDecay
  exact (inv_le_one₀ (by positivity : 0 < 1 + r ^ 2)).2
    (by nlinarith [sq_nonneg r])

theorem scaleGreenODEField_lipschitz (r : ℝ) :
    LipschitzWith (15 : NNReal) (scaleGreenODEField r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [scaleGreenODEField, Real.dist_eq]
  have ha0 : 0 ≤ weightedGreenDecay r := weightedGreenDecay_nonneg r
  have ha1 : weightedGreenDecay r ≤ 1 := weightedGreenDecay_le_one r
  have hcoef : |15 * weightedGreenDecay r ^ 2| ≤ (15 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 15 * weightedGreenDecay r ^ 2)]
    nlinarith [sq_nonneg (weightedGreenDecay r),
      mul_self_le_mul_self ha0 ha1]
  apply max_le
  · calc
      |x.2 - y.2| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_right _ _
      _ ≤ 15 * max |x.1 - y.1| |x.2 - y.2| := by
        have hm : 0 ≤ max |x.1 - y.1| |x.2 - y.2| :=
          le_trans (abs_nonneg _) (le_max_left _ _)
        nlinarith
  · calc
      |-15 * weightedGreenDecay r ^ 2 * x.1 -
          -15 * weightedGreenDecay r ^ 2 * y.1| =
          |-(15 * weightedGreenDecay r ^ 2 * (x.1 - y.1))| := by
        congr 1
        ring
      _ = |15 * weightedGreenDecay r ^ 2| * |x.1 - y.1| := by
        rw [abs_neg, abs_mul]
      _ ≤ 15 * max |x.1 - y.1| |x.2 - y.2| := by
        exact mul_le_mul hcoef (le_max_left _ _)
          (abs_nonneg _) (by norm_num)

theorem resonancePlus_deriv_zero :
    deriv resonancePlus 0 = 1 / 2 := by
  rw [resonancePlus_deriv_eq]
  have hminus : deriv resonanceMinus 0 = 1 := by
    change deriv (radialU bubble) 0 = 1
    rw [radialU_bubble_deriv_closed]
    simp [bubbleRadialEnergyDerivative]
  rw [hminus]
  norm_num

/-- Phase-space representative of the continuous Green primitive. -/
def greenODEState (h : ℝ → ℝ) (r : ℝ) : ℝ × ℝ :=
  (halfLineMinGreen h r, halfLineGreenTail h r)

theorem greenODEState_hasDerivWithinAt
    {h : ℝ → ℝ} (hcont : Continuous h)
    (hh : IntegrableOn h (Ioi (0 : ℝ)))
    {r : ℝ} (hr : 0 ≤ r) :
    HasDerivWithinAt (greenODEState h)
      (halfLineGreenTail h r, -h r) (Ici r) r := by
  rcases hr.eq_or_lt with rfl | hr
  · exact (halfLineMinGreen_hasDerivWithinAt_zero hcont hh).prodMk
      (halfLineGreenTail_hasDerivWithinAt_zero hcont hh)
  · exact (halfLineMinGreen_hasDerivAt hcont hh hr).hasDerivWithinAt.prodMk
      (halfLineGreenTail_hasDerivAt hcont hh hr).hasDerivWithinAt

/-- The Green state attached to a `1/15` eigenvector solves the scale ODE. -/
theorem greenODEState_one_fifteen_hasDerivWithinAt
    (f : RealL2 halfLineMeasure)
    (heig : weightedFreeGreenOperator f = (1 / 15 : ℝ) • f)
    {r : ℝ} (hr : 0 ≤ r) :
    HasDerivWithinAt
      (greenODEState (weightedGreenEigenSource (1 / 15 : ℝ) f))
      (scaleGreenODEField r
        (greenODEState (weightedGreenEigenSource (1 / 15 : ℝ) f) r))
      (Ici r) r := by
  have hbase := greenODEState_hasDerivWithinAt
    (weightedGreenEigenSource_continuous (1 / 15 : ℝ) f)
    (weightedGreenEigenSource_integrableOn (by norm_num) f heig) hr
  convert hbase using 1
  unfold scaleGreenODEField greenODEState
  rw [weightedGreenEigenSource_one_fifteen,
    weightedGreenPrimitive_eq_eigen_minGreen (by norm_num) f heig]
  simp only [Prod.fst, Prod.snd]
  ring

/-- Phase-space form of a scalar multiple of the explicit scale resonance. -/
def scaleResonanceODEState (c : ℝ) (r : ℝ) : ℝ × ℝ :=
  (c * resonancePlus r, c * deriv resonancePlus r)

theorem scaleResonanceODEState_hasDerivAt (c r : ℝ) :
    HasDerivAt (scaleResonanceODEState c)
      (scaleGreenODEField r (scaleResonanceODEState c r)) r := by
  have hpsi : ContDiff ℝ ∞ resonancePlus := resonancePlus_contDiff_infty
  have hpsi1 : ContDiff ℝ ∞ (deriv resonancePlus) :=
    (contDiff_infty_iff_deriv.mp hpsi).2
  have hD : HasDerivAt (fun x : ℝ => c * resonancePlus x)
      (c * deriv resonancePlus r) r :=
    ((contDiff_infty_iff_deriv.mp hpsi).1 r).hasDerivAt.const_mul c
  have hDD : HasDerivAt (fun x : ℝ => c * deriv resonancePlus x)
      (c * deriv (deriv resonancePlus) r) r :=
    ((contDiff_infty_iff_deriv.mp hpsi1).1 r).hasDerivAt.const_mul c
  convert hD.prodMk hDD using 1
  · rfl
  · unfold scaleGreenODEField scaleResonanceODEState weightedGreenDecay
    apply Prod.ext
    · rfl
    · simp only [Prod.fst, Prod.snd]
      have hsecond : deriv (deriv resonancePlus) r =
          -15 * (1 + r ^ 2)⁻¹ ^ 2 * resonancePlus r := by
        have h := resonancePlus_second_eq_weight r
        linarith
      rw [hsecond]
      ring

theorem greenODEState_continuousOn_Icc
    {h : ℝ → ℝ} (hcont : Continuous h)
    (hh : IntegrableOn h (Ioi (0 : ℝ))) (R : ℝ) :
    ContinuousOn (greenODEState h) (Icc 0 R) := by
  intro r hr
  rcases hr.1.eq_or_lt with rfl | hrpos
  · exact (greenODEState_hasDerivWithinAt hcont hh (le_refl 0)).continuousWithinAt.mono
      (fun _ hx => hx.1)
  · exact ((halfLineMinGreen_hasDerivAt hcont hh hrpos).prodMk
      (halfLineGreenTail_hasDerivAt hcont hh hrpos)).continuousAt.continuousWithinAt

theorem scaleResonanceODEState_continuousOn (c : ℝ) (s : Set ℝ) :
    ContinuousOn (scaleResonanceODEState c) s := by
  exact ((continuous_const.mul resonancePlus_contDiff_infty.continuous).prodMk
    (continuous_const.mul
      ((contDiff_infty_iff_deriv.mp resonancePlus_contDiff_infty).2.continuous))).continuousOn

/-- Every `1/15` Green eigenvector has a primitive proportional to the
explicit scale resonance. -/
theorem weightedGreenPrimitive_one_fifteen_eq_resonance
    (f : RealL2 halfLineMeasure)
    (heig : weightedFreeGreenOperator f = (1 / 15 : ℝ) • f) :
    ∃ c : ℝ, ∀ r : ℝ, 0 ≤ r →
      weightedGreenPrimitive f r = c * resonancePlus r := by
  let h : ℝ → ℝ := weightedGreenEigenSource (1 / 15 : ℝ) f
  let c : ℝ := 2 * halfLineGreenTail h 0
  refine ⟨c, ?_⟩
  intro r hr
  let R : ℝ := r + 1
  have hR : r ∈ Icc (0 : ℝ) R := by
    constructor
    · exact hr
    · dsimp [R]
      linarith
  have huniq : EqOn (greenODEState h) (scaleResonanceODEState c)
      (Icc (0 : ℝ) R) := by
    apply ODE_solution_unique (K := (15 : NNReal))
        (v := scaleGreenODEField)
    · exact scaleGreenODEField_lipschitz
    · exact greenODEState_continuousOn_Icc
        (weightedGreenEigenSource_continuous (1 / 15 : ℝ) f)
        (weightedGreenEigenSource_integrableOn (by norm_num) f heig) R
    · intro t ht
      exact greenODEState_one_fifteen_hasDerivWithinAt f heig ht.1
    · exact scaleResonanceODEState_continuousOn c (Icc 0 R)
    · intro t _
      exact (scaleResonanceODEState_hasDerivAt c t).hasDerivWithinAt
    · unfold greenODEState scaleResonanceODEState c
      ext
      · simp
      · rw [resonancePlus_deriv_zero]
        ring
  have heq := congrArg Prod.fst (huniq hR)
  dsimp [greenODEState, scaleResonanceODEState] at heq
  dsimp [h] at heq
  rw [← weightedGreenPrimitive_eq_eigen_minGreen (by norm_num) f heig] at heq
  exact heq

/-- The distinguished Green eigenspace is at most one-dimensional. -/
theorem weightedFreeGreen_one_fifteen_eigen_mem_span
    (f : RealL2 halfLineMeasure)
    (heig : weightedFreeGreenOperator f = (1 / 15 : ℝ) • f) :
    f ∈ Submodule.span ℝ {weightedScaleResonanceL2} := by
  obtain ⟨c, hq⟩ :=
    weightedGreenPrimitive_one_fifteen_eq_resonance f heig
  refine Submodule.mem_span_singleton.mpr ⟨15 * c, ?_⟩
  apply Lp.ext
  have hpoint := weightedFreeGreenOperator_ae_pointwise f
  rw [heig] at hpoint
  filter_upwards [hpoint, Lp.coeFn_smul (1 / 15 : ℝ) f,
      Lp.coeFn_smul (15 * c) weightedScaleResonanceL2,
      weightedScaleResonanceL2_ae,
      ae_restrict_mem measurableSet_Ioi]
      with r hpoint hsmall hlarge hx0 hr
  rw [hsmall] at hpoint
  simp only [Pi.smul_apply, smul_eq_mul] at hpoint
  rw [hlarge]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hx0, weightedScaleResonance_closed]
  unfold weightedFreeGreenPointwise at hpoint
  rw [hq r hr.le] at hpoint
  unfold weightedGreenDecay at hpoint
  calc
    15 * c * ((1 + r ^ 2)⁻¹ * resonancePlus r) =
        15 * ((1 + r ^ 2)⁻¹ * (c * resonancePlus r)) := by ring
    _ = f r := by linarith

theorem weightedFreeGreenOperator_scale_eigen_normalized :
    weightedFreeGreenOperator weightedScaleResonanceL2 =
      (1 / 15 : ℝ) • weightedScaleResonanceL2 := by
  have h15 : (15 : ℝ) •
      weightedFreeGreenOperator weightedScaleResonanceL2 =
      weightedScaleResonanceL2 := by
    calc
      (15 : ℝ) • weightedFreeGreenOperator weightedScaleResonanceL2 =
          weightedFreeGreenOperator
            ((15 : ℝ) • weightedScaleResonanceL2) := by
        rw [map_smul]
      _ = weightedScaleResonanceL2 :=
        weightedFreeGreenOperator_scale_eigen
  calc
    weightedFreeGreenOperator weightedScaleResonanceL2 =
        (1 / 15 : ℝ) •
          ((15 : ℝ) • weightedFreeGreenOperator weightedScaleResonanceL2) := by
      module
    _ = (1 / 15 : ℝ) • weightedScaleResonanceL2 := by rw [h15]

/-- Exact classification of the `1/15` eigenspace of the weighted free
Green operator. -/
theorem weightedFreeGreen_one_fifteen_eigen_iff
    (f : RealL2 halfLineMeasure) :
    weightedFreeGreenOperator f = (1 / 15 : ℝ) • f ↔
      f ∈ Submodule.span ℝ {weightedScaleResonanceL2} := by
  constructor
  · exact weightedFreeGreen_one_fifteen_eigen_mem_span f
  · intro hf
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
    rw [map_smul, weightedFreeGreenOperator_scale_eigen_normalized]
    module

end HBL.Modulation.Monopole
