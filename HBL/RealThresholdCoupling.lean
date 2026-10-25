import HBL.TriangularThresholdCoupling
import HBL.PhysicalRadial3PhaseCore
import Mathlib.MeasureTheory.Integral.Prod

/-!
Actual real-channel threshold observation for the triangular repair.

A compact radial testing profile g gives zeta=r*g and q_g=(r*g)'.
The bounded functional below is constructed from the existing actual
Volterra operator Aplus. Its identification with the tested differential
operator Hplus includes the original nonlocal Hartree kernel, absolute
product integrability, Fubini and the finite-interval Green identity.
No unweighted L2 hypothesis on r*f, no generator inverse and no exact
zero/centre splitting is used. This is a tested half-line identity, not
an evolution theorem or the full three-dimensional angular reduction.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology RealInnerProductSpace

namespace HBL.Modulation.TriangularRepair

open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Modulation.Monopole

private theorem cap_integral
    (F : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hzero : ∀ r : ℝ, R < r → F r = 0) :
    (∫ r : ℝ, F r ∂halfLineMeasure) = ∫ r in (0 : ℝ)..R, F r := by
  change (∫ r in Ioi (0 : ℝ), F r) = _
  rw [intervalIntegral.integral_of_le hR]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc (0 : ℝ) R ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
  intro r hr
  have hrt : R < r := by
    by_contra h
    exact hr.2 ⟨hr.1, le_of_not_gt h⟩
  exact hzero r hrt

private theorem test_deriv_zero (g : ℝ → ℝ) {R r : ℝ}
    (hcut : ∀ t : ℝ, R ≤ t → g t = 0) (hr : R < r) :
    deriv (radialU g) r = 0 := by
  have he : radialU g =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    simp only [radialU, hcut t ht.le, mul_zero]
  exact ((hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq he).deriv

private theorem potential_continuous_real : Continuous potential := by
  unfold potential
  apply Continuous.div continuous_const (by fun_prop)
  intro r
  positivity

private theorem kinetic_green
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (R : ℝ) (hgR : g R = 0) :
    (∫ r in (0 : ℝ)..R, radialU g r * (-deriv (deriv (radialU f)) r)) =
      ∫ r in (0 : ℝ)..R, deriv (radialU f) r * deriv (radialU g) r := by
  have hu : ContDiff ℝ 2 (radialU f) := contDiff_id.mul hf
  have hv : ContDiff ℝ 2 (radialU g) := contDiff_id.mul hg
  have hdu : ContDiff ℝ 1 (deriv (radialU f)) := hu.deriv'
  have hdv : ContDiff ℝ 1 (deriv (radialU g)) := hv.deriv'
  have hp : Continuous (fun r => deriv (radialU g) r * deriv (radialU f) r) :=
    hdv.continuous.mul hdu.continuous
  have ht : Continuous (fun r => radialU g r * deriv (deriv (radialU f)) r) :=
    hv.continuous.mul hdu.continuous_deriv_one
  have hpi := hp.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hti := ht.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => ((hv.differentiable (by norm_num) r).hasDerivAt).mul
      ((hdu.differentiable (by norm_num) r).hasDerivAt)) (hpi.add hti)
  have hzero :
      (∫ r in (0 : ℝ)..R, deriv (radialU g) r * deriv (radialU f) r) +
      (∫ r in (0 : ℝ)..R, radialU g r * deriv (deriv (radialU f)) r) = 0 := by
    rw [intervalIntegral.integral_add hpi hti] at hFTC
    simpa only [Pi.mul_apply, radialU, hgR, mul_zero, zero_mul, sub_zero] using hFTC
  calc
    (∫ r in (0 : ℝ)..R, radialU g r * (-deriv (deriv (radialU f)) r)) =
        -(∫ r in (0 : ℝ)..R, radialU g r * deriv (deriv (radialU f)) r) := by
      simp only [mul_neg, intervalIntegral.integral_neg]
    _ = ∫ r in (0 : ℝ)..R, deriv (radialU g) r * deriv (radialU f) r := by
      linarith
    _ = ∫ r in (0 : ℝ)..R, deriv (radialU f) r * deriv (radialU g) r := by
      apply intervalIntegral.integral_congr
      intro r _
      exact mul_comm _ _

private theorem nonlocal_inner_integral (f g : ℝ → ℝ) (r : ℝ) :
    (∫ s : ℝ, hartreeKernel r s * (radialU g r * radialU f s)
      ∂halfLineMeasure) = radialU g r * nonlocalApply (radialU f) r := by
  change (∫ s in Ioi (0 : ℝ), hartreeKernel r s * (radialU g r * radialU f s)) =
    radialU g r * ∫ s in Ioi (0 : ℝ), hartreeKernel r s * radialU f s
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by ring)

private theorem nonlocal_pairing_integrable
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hgmem : MemLp (deriv (radialU g)) 2 halfLineMeasure) :
    Integrable (fun r => radialU g r * nonlocalApply (radialU f) r)
      halfLineMeasure := by
  have hprod := hartreeProfileForm_integrable (radialU f) (radialU g)
    (weightedRadialU_memLp f hf hfmem) (weightedRadialU_memLp g hg hgmem)
  exact hprod.integral_prod_left.congr
    (Filter.Eventually.of_forall (fun r => nonlocal_inner_integral f g r))

private theorem nonlocal_pairing_fubini
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hgmem : MemLp (deriv (radialU g)) 2 halfLineMeasure) :
    (∫ p : ℝ × ℝ, hartreeKernel p.1 p.2 * (radialU g p.1 * radialU f p.2)
      ∂(halfLineMeasure.prod halfLineMeasure)) =
      ∫ r : ℝ, radialU g r * nonlocalApply (radialU f) r ∂halfLineMeasure := by
  rw [integral_prod _ (hartreeProfileForm_integrable (radialU f) (radialU g)
    (weightedRadialU_memLp f hf hfmem) (weightedRadialU_memLp g hg hgmem))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun r => nonlocal_inner_integral f g r)

/-- Concrete compact test coordinate; its L2 membership is proved from
regularity and support rather than imposed as an additional hypothesis. -/
def realTestCoordinate (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (R : ℝ) (hR : 0 ≤ R) (hcut : ∀ r : ℝ, R ≤ r → g r = 0) :
    FullRadialEnergyL2 :=
  smoothToRadialDotH1 g
    (radialU_deriv_memLp_of_upperSupport g (hg.of_le (by norm_num)) R hR hcut)

/-- A bounded observation of the actual nonlocal real channel, with the
Hamiltonian derivative remaining in the tested integral, not on inputs. -/
def realThresholdCoupling (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (R : ℝ) (hR : 0 ≤ R) (hcut : ∀ r : ℝ, R ≤ r → g r = 0) :
    FullRadialEnergyL2 →L[ℝ] ℝ :=
  (innerSL ℝ (realTestCoordinate g hg R hR hcut)).comp weightedVolterraAPlus

private theorem actual_real_coupling_identity
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (R : ℝ) (hR : 0 ≤ R) (hcut : ∀ r : ℝ, R ≤ r → g r = 0)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure) :
    (∫ r in (0 : ℝ)..R, radialU g r * hPlusApply (radialU f) r) =
      realThresholdCoupling g hg R hR hcut (smoothToRadialDotH1 f hfmem) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  let hgmem := radialU_deriv_memLp_of_upperSupport g hg1 R hR hcut
  have hkin := kinetic_green f g hf hg R (hcut R le_rfl)
  have hcapD := cap_integral
    (fun r => deriv (radialU f) r * deriv (radialU g) r) R hR
    (fun r hr => by rw [test_deriv_zero g hcut hr, mul_zero])
  have hcapV := cap_integral
    (fun r => weightedGreenDecay r ^ 2 * radialU f r * radialU g r) R hR
    (fun r hr => by simp only [radialU, hcut r hr.le, mul_zero])
  have hcapN := cap_integral
    (fun r => radialU g r * nonlocalApply (radialU f) r) R hR
    (fun r hr => by simp only [radialU, hcut r hr.le, mul_zero, zero_mul])
  have hpot :
      (∫ r in (0 : ℝ)..R, radialU g r * (3 * potential r * radialU f r)) =
        9 * (∫ r in (0 : ℝ)..R,
          weightedGreenDecay r ^ 2 * radialU f r * radialU g r) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp [potential, weightedGreenDecay]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  have hu : ContDiff ℝ 2 (radialU f) := contDiff_id.mul hf
  have hv : ContDiff ℝ 2 (radialU g) := contDiff_id.mul hg
  have hdu : ContDiff ℝ 1 (deriv (radialU f)) := hu.deriv'
  have hkI := (hv.continuous.mul hdu.continuous_deriv_one.neg).intervalIntegrable
    (μ := volume) (a := (0 : ℝ)) (b := R)
  have hpC : Continuous
      (fun r => radialU g r * (3 * potential r * radialU f r)) :=
    hv.continuous.mul ((continuous_const.mul potential_continuous_real).mul hu.continuous)
  have hpI := hpC.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hnI : IntervalIntegrable
      (fun r => radialU g r * nonlocalApply (radialU f) r) volume 0 R := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).2
    exact (nonlocal_pairing_integrable f g hf1 hg1 hfmem hgmem).mono_measure
      (finiteRadialMeasure_le_full R)
  have hsplit :
      (∫ r in (0 : ℝ)..R, radialU g r * hPlusApply (radialU f) r) =
        (∫ r in (0 : ℝ)..R, radialU g r * (-deriv (deriv (radialU f)) r)) -
        (∫ r in (0 : ℝ)..R, radialU g r * (3 * potential r * radialU f r)) -
        (∫ r in (0 : ℝ)..R, radialU g r * nonlocalApply (radialU f) r) := by
    simp only [hPlusApply, mul_sub]
    rw [intervalIntegral.integral_sub (hkI.sub hpI) hnI,
      intervalIntegral.integral_sub hkI hpI]
  have hpair := weightedVolterraAPlus_radial_profile_pairing f g hf1 hg1 hfmem hgmem
  rw [hcapD, hcapV, nonlocal_pairing_fubini f g hf1 hg1 hfmem hgmem, hcapN] at hpair
  change _ = inner ℝ (realTestCoordinate g hg R hR hcut)
    (weightedVolterraAPlus (smoothToRadialDotH1 f hfmem))
  rw [real_inner_comm]
  change _ = inner ℝ (weightedVolterraAPlus (smoothToRadialDotH1 f hfmem))
    (smoothToRadialDotH1 g hgmem)
  rw [hpair, hsplit, hkin, hpot]
  ring

private theorem real_coupling_bound
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (R : ℝ) (hR : 0 ≤ R) (hcut : ∀ r : ℝ, R ≤ r → g r = 0)
    (q : FullRadialEnergyL2) :
    |realThresholdCoupling g hg R hR hcut q| ≤
      (‖realTestCoordinate g hg R hR hcut‖ * ‖weightedVolterraAPlus‖) * ‖q‖ := by
  change |inner ℝ (realTestCoordinate g hg R hR hcut) (weightedVolterraAPlus q)| ≤ _
  calc
    |inner ℝ (realTestCoordinate g hg R hR hcut) (weightedVolterraAPlus q)| ≤
        ‖realTestCoordinate g hg R hR hcut‖ * ‖weightedVolterraAPlus q‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖realTestCoordinate g hg R hR hcut‖ * (‖weightedVolterraAPlus‖ * ‖q‖) :=
      mul_le_mul_of_nonneg_left (weightedVolterraAPlus.le_opNorm q) (norm_nonneg _)
    _ = (‖realTestCoordinate g hg R hR hcut‖ * ‖weightedVolterraAPlus‖) * ‖q‖ :=
      (mul_assoc _ _ _).symm

/-- Complete real-channel tested-generator theorem. The original Hartree
pairing is absolutely integrable; the actual Hplus integral equals a
constructed energy-bounded functional, with a quantitative two-input
estimate. No unweighted L2 assumption on r*f is present. -/
theorem realThresholdCoupling_certified
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (R : ℝ) (hR : 0 ≤ R) (hcut : ∀ r : ℝ, R ≤ r → g r = 0) :
    (∀ (f : ℝ → ℝ) (_hf : ContDiff ℝ 2 f)
      (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure),
      Integrable (fun p : ℝ × ℝ =>
        hartreeKernel p.1 p.2 * (radialU g p.1 * radialU f p.2))
        (halfLineMeasure.prod halfLineMeasure) ∧
      (∫ r in (0 : ℝ)..R, radialU g r * hPlusApply (radialU f) r) =
        realThresholdCoupling g hg R hR hcut (smoothToRadialDotH1 f hfmem)) ∧
    (∀ q : FullRadialEnergyL2,
      |realThresholdCoupling g hg R hR hcut q| ≤
        (‖realTestCoordinate g hg R hR hcut‖ * ‖weightedVolterraAPlus‖) * ‖q‖) ∧
    (∀ q p : FullRadialEnergyL2,
      |realThresholdCoupling g hg R hR hcut q -
        realThresholdCoupling g hg R hR hcut p| ≤
        (‖realTestCoordinate g hg R hR hcut‖ * ‖weightedVolterraAPlus‖) * ‖q - p‖) := by
  refine ⟨?_, real_coupling_bound g hg R hR hcut, ?_⟩
  · intro f hf hfmem
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
    exact ⟨hartreeProfileForm_integrable (radialU f) (radialU g)
      (weightedRadialU_memLp f hf1 hfmem)
      (weightedRadialU_memLp g hg1
        (radialU_deriv_memLp_of_upperSupport g hg1 R hR hcut)),
      actual_real_coupling_identity g hg R hR hcut f hf hfmem⟩
  · intro q p
    rw [← map_sub]
    exact real_coupling_bound g hg R hR hcut (q - p)

end HBL.Modulation.TriangularRepair
