import HBL.HartreeKernelShortRange

/-!
A reusable product-L2 criterion for radial logarithmic kernels.

The diagonal estimate is the same one used for the Hartree short-range
kernel.  This formulation separates the analytic logarithmic singularity
from the particular radial weight and is used below for the weighted
Birman--Schwinger kernel.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- Near-diagonal majorant associated with a square weight `w` and its
square-root moment `v`. -/
def productLogSqNearMajorant
    (w v : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  v p.1 * w p.2 * diagonalSqrtKernel (p.1 - p.2) +
    w p.1 * v p.2 * diagonalSqrtKernel (p.1 - p.2)

/-- Complementary majorant away from the logarithmic diagonal. -/
def productLogSqFarMajorant
    (w v : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  v p.1 * w p.2 + w p.1 * v p.2

theorem productLogSqNearMajorant_nonneg
    (w v : ℝ → ℝ) (hw : ∀ r, 0 ≤ w r) (hv : ∀ r, 0 ≤ v r)
    (p : ℝ × ℝ) :
    0 ≤ productLogSqNearMajorant w v p := by
  unfold productLogSqNearMajorant
  exact add_nonneg
    (mul_nonneg (mul_nonneg (hv _) (hw _)) (diagonalSqrtKernel_nonneg _))
    (mul_nonneg (mul_nonneg (hw _) (hv _)) (diagonalSqrtKernel_nonneg _))

theorem productLogSqFarMajorant_nonneg
    (w v : ℝ → ℝ) (hw : ∀ r, 0 ≤ w r) (hv : ∀ r, 0 ≤ v r)
    (p : ℝ × ℝ) :
    0 ≤ productLogSqFarMajorant w v p := by
  unfold productLogSqFarMajorant
  exact add_nonneg (mul_nonneg (hv _) (hw _)) (mul_nonneg (hw _) (hv _))

theorem productLogSqNearMajorant_integrable
    (w v : ℝ → ℝ) (hw : Integrable w) (hv : Integrable v)
    (hw_one : ∀ r, ‖w r‖ ≤ 1) (hv_one : ∀ r, ‖v r‖ ≤ 1) :
    Integrable (productLogSqNearMajorant w v) (volume.prod volume) := by
  have hconvw : Integrable
      (fun p : ℝ × ℝ => w p.2 * diagonalSqrtKernel (p.1 - p.2))
      (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      hw.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
        diagonalSqrtKernel_integrable
  have hconvv : Integrable
      (fun p : ℝ × ℝ => v p.2 * diagonalSqrtKernel (p.1 - p.2))
      (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      hv.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
        diagonalSqrtKernel_integrable
  have hnearw := hconvw.bdd_mul
    (hv.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst)
    (Filter.Eventually.of_forall fun p : ℝ × ℝ => hv_one p.1)
  have hnearv := hconvv.bdd_mul
    (hw.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst)
    (Filter.Eventually.of_forall fun p : ℝ × ℝ => hw_one p.1)
  change Integrable (fun p : ℝ × ℝ =>
    v p.1 * w p.2 * diagonalSqrtKernel (p.1 - p.2) +
      w p.1 * v p.2 * diagonalSqrtKernel (p.1 - p.2))
      (volume.prod volume)
  refine (hnearw.add hnearv).congr ?_
  filter_upwards with p
  simp only [Function.comp_apply, Pi.add_apply]
  ring

theorem productLogSqFarMajorant_integrable
    (w v : ℝ → ℝ) (hw : Integrable w) (hv : Integrable v) :
    Integrable (productLogSqFarMajorant w v) (volume.prod volume) := by
  exact (hv.mul_prod hw).add (hw.mul_prod hv)

/-- A product kernel with the radial logarithm belongs to product L2 once
its squared radial weight and first square-root moment are integrable and
bounded. -/
theorem product_log_kernel_sq_integrable
    (u w v : ℝ → ℝ) (C : ℝ)
    (hw_nonneg : ∀ r, 0 ≤ w r) (hv_nonneg : ∀ r, 0 ≤ v r)
    (hw : Integrable w) (hv : Integrable v)
    (hw_one : ∀ r, ‖w r‖ ≤ 1) (hv_one : ∀ r, ‖v r‖ ≤ 1)
    (hv_eq : ∀ r, v r = Real.sqrt r * w r)
    (hu_sq : ∀ r, 0 < r → u r ^ 2 = w r)
    (hmeas : Measurable (Function.uncurry (fun r rho =>
      C * u r * u rho * hartreeRadialLog r rho))) :
    Integrable (fun p : ℝ × ℝ =>
      (C * u p.1 * u p.2 * hartreeRadialLog p.1 p.2) ^ 2)
      (halfLineMeasure.prod halfLineMeasure) := by
  let near := productLogSqNearMajorant w v
  let far := productLogSqFarMajorant w v
  let majorant : ℝ × ℝ → ℝ := fun p =>
    16 * |C| ^ 2 * (near p + far p)
  have hnear : Integrable near (volume.prod volume) :=
    productLogSqNearMajorant_integrable w v hw hv hw_one hv_one
  have hfar : Integrable far (volume.prod volume) :=
    productLogSqFarMajorant_integrable w v hw hv
  have hmajor : Integrable majorant (volume.prod volume) := by
    exact (hnear.add hfar).const_mul (16 * |C| ^ 2)
  rw [Measure.prod_restrict]
  refine hmajor.integrableOn.mono'
    ((hmeas.pow_const 2).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hlog := hartreeRadialLog_sq_sqrt_bound p.1 p.2 hp.1 hp.2
  have hfac : 0 ≤ |C| ^ 2 * w p.1 * w p.2 := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hw_nonneg _)) (hw_nonneg _)
  have hsq :
      (C * u p.1 * u p.2 * hartreeRadialLog p.1 p.2) ^ 2 =
        |C| ^ 2 * w p.1 * w p.2 * hartreeRadialLog p.1 p.2 ^ 2 := by
    calc
      (C * u p.1 * u p.2 * hartreeRadialLog p.1 p.2) ^ 2 =
          C ^ 2 * u p.1 ^ 2 * u p.2 ^ 2 *
            hartreeRadialLog p.1 p.2 ^ 2 := by ring
      _ = |C| ^ 2 * w p.1 * w p.2 *
            hartreeRadialLog p.1 p.2 ^ 2 := by
        rw [hu_sq p.1 hp.1, hu_sq p.2 hp.2, sq_abs]
  rw [hsq]
  by_cases hdiag : |p.1 - p.2| < 1
  · have hk : diagonalSqrtKernel (p.1 - p.2) =
        (Real.sqrt |p.1 - p.2|)⁻¹ := by
      simp [diagonalSqrtKernel, hdiag]
    calc
      |C| ^ 2 * w p.1 * w p.2 * hartreeRadialLog p.1 p.2 ^ 2 ≤
          (|C| ^ 2 * w p.1 * w p.2) *
            (16 * (Real.sqrt p.1 + Real.sqrt p.2) *
              (Real.sqrt |p.1 - p.2|)⁻¹) :=
        mul_le_mul_of_nonneg_left hlog hfac
      _ = 16 * |C| ^ 2 * near p := by
        dsimp [near, productLogSqNearMajorant]
        rw [hk, hv_eq p.1, hv_eq p.2]
        ring
      _ ≤ majorant p := by
        dsimp [majorant]
        gcongr
        exact le_add_of_nonneg_right
          (productLogSqFarMajorant_nonneg w v hw_nonneg hv_nonneg p)
  · have hfar_one : 1 ≤ |p.1 - p.2| := le_of_not_gt hdiag
    have hsqrt : 1 ≤ Real.sqrt |p.1 - p.2| := by
      simpa using Real.sqrt_le_sqrt hfar_one
    have hinv : (Real.sqrt |p.1 - p.2|)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by positivity : 0 < Real.sqrt |p.1 - p.2|)).2 hsqrt
    have hlogfar : hartreeRadialLog p.1 p.2 ^ 2 ≤
        16 * (Real.sqrt p.1 + Real.sqrt p.2) := by
      calc
        hartreeRadialLog p.1 p.2 ^ 2 ≤
            16 * (Real.sqrt p.1 + Real.sqrt p.2) *
              (Real.sqrt |p.1 - p.2|)⁻¹ := hlog
        _ ≤ 16 * (Real.sqrt p.1 + Real.sqrt p.2) := by
          nlinarith [Real.sqrt_nonneg p.1, Real.sqrt_nonneg p.2]
    calc
      |C| ^ 2 * w p.1 * w p.2 * hartreeRadialLog p.1 p.2 ^ 2 ≤
          (|C| ^ 2 * w p.1 * w p.2) *
            (16 * (Real.sqrt p.1 + Real.sqrt p.2)) :=
        mul_le_mul_of_nonneg_left hlogfar hfac
      _ = 16 * |C| ^ 2 * far p := by
        dsimp [far, productLogSqFarMajorant]
        rw [hv_eq p.1, hv_eq p.2]
        ring
      _ ≤ majorant p := by
        dsimp [majorant]
        gcongr
        exact le_add_of_nonneg_left
          (productLogSqNearMajorant_nonneg w v hw_nonneg hv_nonneg p)

end HBL.Modulation.AffineTail
