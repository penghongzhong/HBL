import HBL.HartreeDensitySourceBounds
import HBL.HartreeLocalCutoff

/-!
# A differentiated quadratic Hartree density remainder

Reuse the exact physical expansion and the noncompact convolution derivative.
For Q = |w+h|^4 - |w|^4 - 4 w^3 Re h, prove the ACTUAL spatial differential
and retain quadratic smallness in h and Dh. The background is real C1 and
bounded with bounded derivative. Neither its L2 nor its L4 norm is required
for this quadratic density remainder. No compact support or approximation
sequence is an input.

This is the differentiated nonlocal density part of the Taylor remainder,
not yet the full seventh-order remainder difference or a constrained flow.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Topology

namespace HBL.RegularRadiation.PhysicalExpansion
open SpatialCompletion LocalCutoff

/-- A single explicit coefficient for the quadratic gradient estimate. -/
def densityGradientQuadraticConstant (M L r : ℝ) : ℝ :=
  4 * L * (3 * M + r) + 4 * (M ^ 2 + (2 * M + r) * (M + r))

private theorem increment_bound (a : ℝ) (z : ℂ) {M r : ℝ}
    (hM : 0 ≤ M) (ha : |a| ≤ M) (hz : ‖z‖ ≤ r) :
    |2 * a * z.re + ‖z‖ ^ 2| ≤ (2 * M + r) * ‖z‖ := by
  calc
    _ ≤ |2 * a * z.re| + |‖z‖ ^ 2| := abs_add_le _ _
    _ = 2 * |a| * |z.re| + ‖z‖ ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sq_nonneg ‖z‖)]
    _ ≤ (2 * M) * ‖z‖ + r * ‖z‖ := by
      exact add_le_add
        (mul_le_mul (by linarith : 2 * |a| ≤ 2 * M)
          (Complex.abs_re_le_norm z) (abs_nonneg _) (by positivity))
        (by nlinarith only [mul_le_mul_of_nonneg_right hz (norm_nonneg z)])
    _ = _ := by ring

private theorem density_value_bound (a : ℝ) (z : ℂ) {M r : ℝ}
    (hM : 0 ≤ M) (ha : |a| ≤ M) (hz : ‖z‖ ≤ r) :
    ‖((2 * a ^ 2 * ‖z‖ ^ 2 + (2 * a * z.re + ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ)‖ ≤
      densityQuadraticConstant M r * ‖z‖ ^ 2 := by
  have ha2 : a ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hs := pow_le_pow_left₀ (abs_nonneg _) (increment_bound a z hM ha hz) 2
  simp only [sq_abs, mul_pow] at hs
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  unfold densityQuadraticConstant
  nlinarith only [hs, mul_le_mul_of_nonneg_right ha2 (sq_nonneg ‖z‖)]

/-- The actual quadratic density is C1, independently of convolution theory. -/
theorem densityRemainder_contDiff (w : Space → ℝ) (h : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 1 (densityRemainder w h) := by
  have hn := hh.norm_sq ℂ
  have hre := Complex.reCLM.contDiff.comp hh
  have ha : ContDiff ℝ 1 (fun y => 2 * (w y) ^ 2) := contDiff_const.mul (hw.pow 2)
  have hb : ContDiff ℝ 1 (fun y => 2 * w y) := contDiff_const.mul hw
  exact Complex.ofRealCLM.contDiff.comp
    ((ha.mul hn).add (((hb.mul hre).add hn).pow 2))

/-- Exact differential: every term still contains two perturbation factors
when Dh is counted as one perturbation factor. -/
theorem densityRemainder_fderiv_apply (w : Space → ℝ) (h : Space → ℂ)
    {x : Space} (hw : DifferentiableAt ℝ w x) (hh : DifferentiableAt ℝ h x)
    (v : Space) :
    fderiv ℝ (densityRemainder w h) x v =
      ((4 * w x * (fderiv ℝ w x v) * ‖h x‖ ^ 2 +
        4 * (w x) ^ 2 * inner ℝ (h x) (fderiv ℝ h x v) +
        4 * (2 * w x * (h x).re + ‖h x‖ ^ 2) *
          ((fderiv ℝ w x v) * (h x).re + w x * (fderiv ℝ h x v).re +
            inner ℝ (h x) (fderiv ℝ h x v)) : ℝ) : ℂ) := by
  have hn := hh.hasFDerivAt.norm_sq
  have hre := Complex.reCLM.hasFDerivAt.comp x hh.hasFDerivAt
  have hs := ((hw.hasFDerivAt.const_mul 2).mul hre).add hn
  have hq := (((hw.hasFDerivAt.pow 2).const_mul 2).mul hn).add (hs.pow 2)
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x hq
  simp only [Function.comp_def, Pi.mul_apply, Pi.add_apply, Complex.reCLM_apply] at hd
  change HasFDerivAt (densityRemainder w h) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.reduceSub, pow_one, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    innerSL_apply_apply]
  congr 1
  ring

private theorem scalar_gradient_bound (a b : ℝ) (z k : ℂ)
    {M L r D t : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hD : 0 ≤ D) (ht : 0 ≤ t)
    (ha : |a| ≤ M) (hb : |b| ≤ L * t) (hz : ‖z‖ ≤ r) (hk : ‖k‖ ≤ D * t) :
    |4 * a * b * ‖z‖ ^ 2 + 4 * a ^ 2 * inner ℝ z k +
      4 * (2 * a * z.re + ‖z‖ ^ 2) *
        (b * z.re + a * k.re + inner ℝ z k)| ≤
      (4 * L * (3 * M + r) * ‖z‖ ^ 2 +
        4 * (M ^ 2 + (2 * M + r) * (M + r)) * ‖z‖ * D) * t := by
  have hi : |inner ℝ z k| ≤ ‖z‖ * (D * t) := by
    have h := norm_inner_le_norm (𝕜 := ℝ) z k
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left hk (norm_nonneg z))
  have hbr : |b * z.re| ≤ (L * t) * ‖z‖ := by
    rw [abs_mul]
    exact mul_le_mul hb (Complex.abs_re_le_norm z) (abs_nonneg _) (by positivity)
  have hak : |a * k.re| ≤ M * (D * t) := by
    rw [abs_mul]
    exact mul_le_mul ha ((Complex.abs_re_le_norm k).trans hk) (abs_nonneg _) hM
  have hsum : |b * z.re + a * k.re + inner ℝ z k| ≤
      (L * t) * ‖z‖ + (M + r) * (D * t) := by
    calc
      _ ≤ |b * z.re| + |a * k.re| + |inner ℝ z k| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (L * t) * ‖z‖ + M * (D * t) + ‖z‖ * (D * t) :=
        add_le_add (add_le_add hbr hak) hi
      _ ≤ (L * t) * ‖z‖ + M * (D * t) + r * (D * t) := by gcongr
      _ = _ := by ring
  have h1 : |4 * a * b * ‖z‖ ^ 2| ≤ 4 * M * (L * t) * ‖z‖ ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg (sq_nonneg ‖z‖)]
    gcongr
  have h2 : |4 * a ^ 2 * inner ℝ z k| ≤ 4 * M ^ 2 * (‖z‖ * (D * t)) := by
    rw [abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_pow]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg a) ha 2) (by norm_num))
      hi (abs_nonneg _) (by positivity)
  have h3 : |4 * (2 * a * z.re + ‖z‖ ^ 2) *
      (b * z.re + a * k.re + inner ℝ z k)| ≤
      (4 * ((2 * M + r) * ‖z‖)) *
        ((L * t) * ‖z‖ + (M + r) * (D * t)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (increment_bound a z hM ha hz) (by norm_num))
      hsum (abs_nonneg _) (by positivity)
  calc
    _ ≤ |4 * a * b * ‖z‖ ^ 2| + |4 * a ^ 2 * inner ℝ z k| +
        |4 * (2 * a * z.re + ‖z‖ ^ 2) *
          (b * z.re + a * k.re + inner ℝ z k)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 4 * M * (L * t) * ‖z‖ ^ 2 + 4 * M ^ 2 * (‖z‖ * (D * t)) +
        (4 * ((2 * M + r) * ‖z‖)) *
          ((L * t) * ‖z‖ + (M + r) * (D * t)) :=
      add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- Operator-norm bound retaining the quadratic structure before integration. -/
theorem densityRemainder_fderiv_norm_le (w : Space → ℝ) (h : Space → ℂ)
    {x : Space} (hw : DifferentiableAt ℝ w x) (hh : DifferentiableAt ℝ h x)
    {M L r : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hwb : |w x| ≤ M) (hdw : ‖fderiv ℝ w x‖ ≤ L) (hhb : ‖h x‖ ≤ r) :
    ‖fderiv ℝ (densityRemainder w h) x‖ ≤
      4 * L * (3 * M + r) * ‖h x‖ ^ 2 +
        4 * (M ^ 2 + (2 * M + r) * (M + r)) * ‖h x‖ * ‖fderiv ℝ h x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [densityRemainder_fderiv_apply w h hw hh v, Complex.norm_real, Real.norm_eq_abs]
  apply scalar_gradient_bound (w x) (fderiv ℝ w x v) (h x) (fderiv ℝ h x v)
    hM hL hr (norm_nonneg _) (norm_nonneg _) hwb
  · have hb := (fderiv ℝ w x).le_opNorm v
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hdw (norm_nonneg v))
  · exact hhb
  · exact (fderiv ℝ h x).le_opNorm v

/-- Actual gradient mass and essential bound are quadratic in the perturbation
radius. Neither background L2/L4 nor background gradient L2 is used. -/
theorem densityRemainder_gradient_quadratic
    (w : Space → ℝ) (h : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h)
    (hh2 : MemLp h 2) (hDh2 : MemLp (fderiv ℝ h) 2)
    {M L r : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hwb : ∀ᵐ x, |w x| ≤ M) (hDwb : ∀ᵐ x, ‖fderiv ℝ w x‖ ≤ L)
    (hhb : ∀ᵐ x, ‖h x‖ ≤ r) (hDhb : ∀ᵐ x, ‖fderiv ℝ h x‖ ≤ r)
    (hE : (∫ x : Space, ‖h x‖ ^ 2) ≤ r ^ 2)
    (hED : (∫ x : Space, ‖fderiv ℝ h x‖ ^ 2) ≤ r ^ 2) :
    Integrable (fderiv ℝ (densityRemainder w h)) ∧
    (∫ x : Space, ‖fderiv ℝ (densityRemainder w h) x‖) ≤
      2 * densityGradientQuadraticConstant M L r * r ^ 2 ∧
    (∀ᵐ x, ‖fderiv ℝ (densityRemainder w h) x‖ ≤
      densityGradientQuadraticConstant M L r * r ^ 2) := by
  let A := 4 * L * (3 * M + r)
  let B := 4 * (M ^ 2 + (2 * M + r) * (M + r))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : densityGradientQuadraticConstant M L r = A + B := rfl
  have hb : ∀ᵐ x, ‖fderiv ℝ (densityRemainder w h) x‖ ≤
      A * ‖h x‖ ^ 2 + B * ‖h x‖ * ‖fderiv ℝ h x‖ := by
    filter_upwards [hwb, hDwb, hhb] with x hx hdx hhx
    exact densityRemainder_fderiv_norm_le w h
      (hw.differentiable (by norm_num) x) (hh.differentiable (by norm_num) x)
      hM hL hr hx hdx hhx
  have hdom : ∀ᵐ x, ‖fderiv ℝ (densityRemainder w h) x‖ ≤
      (A + B) * (‖h x‖ ^ 2 + ‖fderiv ℝ h x‖ ^ 2) := by
    filter_upwards [hb] with x hx
    apply hx.trans
    have hm : ‖h x‖ * ‖fderiv ℝ h x‖ ≤ ‖h x‖ ^ 2 + ‖fderiv ℝ h x‖ ^ 2 := by
      nlinarith only [sq_nonneg (‖h x‖ - ‖fderiv ℝ h x‖), sq_nonneg ‖h x‖,
        sq_nonneg ‖fderiv ℝ h x‖]
    have hprod := mul_le_mul_of_nonneg_left hm hB
    nlinarith only [hprod, mul_nonneg hA (sq_nonneg ‖fderiv ℝ h x‖)]
  have hi0 := hh2.norm.integrable_sq
  have hi1 := hDh2.norm.integrable_sq
  have hi : Integrable (fderiv ℝ (densityRemainder w h)) :=
    ((hi0.add hi1).const_mul (A + B)).mono'
      ((densityRemainder_contDiff w h hw hh).continuous_fderiv (by norm_num)).aestronglyMeasurable hdom
  refine ⟨hi, ?_, ?_⟩
  · have hI := integral_mono_ae hi.norm ((hi0.add hi1).const_mul (A + B)) hdom
    rw [integral_const_mul] at hI
    simp only [Pi.add_apply] at hI
    rw [integral_add hi0 hi1] at hI
    rw [hC]
    calc
      _ ≤ (A + B) * ((∫ x : Space, ‖h x‖ ^ 2) +
          ∫ x : Space, ‖fderiv ℝ h x‖ ^ 2) := hI
      _ ≤ (A + B) * (r ^ 2 + r ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hE hED) (add_nonneg hA hB)
      _ = _ := by ring
  · filter_upwards [hb, hhb, hDhb] with x hx hhx hdhx
    rw [hC]
    calc
      _ ≤ A * ‖h x‖ ^ 2 + B * ‖h x‖ * ‖fderiv ℝ h x‖ := hx
      _ ≤ A * r ^ 2 + B * r * r := by gcongr
      _ = _ := by ring

/-- Full noncompact derivative identity and O(r^2) gradient bound for the
quadratic DENSITY potential. The integrability and derivative premises are
proved above from the actual perturbation, not supplied as abstract inputs. -/
theorem densityRemainder_potential_gradient_quadratic
    (w : Space → ℝ) (h : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h)
    (hh2 : MemLp h 2) (hDh2 : MemLp (fderiv ℝ h) 2)
    {M L r : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hwb : ∀ᵐ x, |w x| ≤ M) (hDwb : ∀ᵐ x, ‖fderiv ℝ w x‖ ≤ L)
    (hhb : ∀ᵐ x, ‖h x‖ ≤ r) (hDhb : ∀ᵐ x, ‖fderiv ℝ h x‖ ≤ r)
    (hE : (∫ x : Space, ‖h x‖ ^ 2) ≤ r ^ 2)
    (hED : (∫ x : Space, ‖fderiv ℝ h x‖ ^ 2) ≤ r ^ 2) (x : Space) :
    HasFDerivAt (potential (densityRemainder w h))
      (gradientPotential (fderiv ℝ (densityRemainder w h)) x) x ∧
    Integrable (fun y : Space => (kernel (x - y) : ℂ) •
      fderiv ℝ (densityRemainder w h) y) ∧
    ‖fderiv ℝ (potential (densityRemainder w h)) x‖ ≤
      (nearMass + 2) * densityGradientQuadraticConstant M L r * r ^ 2 := by
  obtain ⟨hDi, hI, hDb⟩ := densityRemainder_gradient_quadratic w h hw hh hh2 hDh2
    hM hL hr hwb hDwb hhb hDhb hE hED
  have hi := (densityRemainder_source_bound w h hw.continuous.aestronglyMeasurable
    hh2 hM hr hwb hhb).1
  have hC : 0 ≤ densityGradientQuadraticConstant M L r := by
    unfold densityGradientQuadraticConstant; positivity
  have hQ : 0 ≤ densityQuadraticConstant M r := by
    unfold densityQuadraticConstant; positivity
  have hρb : ∀ᵐ y, ‖densityRemainder w h y‖ ≤ densityQuadraticConstant M r * r ^ 2 := by
    filter_upwards [hwb, hhb] with y hwy hhy
    exact (density_value_bound (w y) (h y) hM hwy hhy).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hhy 2) hQ)
  have hd := potential_hasFDerivAt_noncompact (densityRemainder w h)
    (densityRemainder_contDiff w h hw hh) hi hDi
    (densityQuadraticConstant M r * r ^ 2)
    (densityGradientQuadraticConstant M L r * r ^ 2)
    (by positivity) (by positivity) hρb hDb x
  have hb := gradientPotential_bound (fderiv ℝ (densityRemainder w h)) hDi
    (densityGradientQuadraticConstant M L r * r ^ 2) (by positivity) hDb x
  refine ⟨hd, hb.1, ?_⟩
  rw [hd.fderiv]
  exact (hb.2.trans (add_le_add le_rfl hI)).trans_eq (by ring)

end HBL.RegularRadiation.PhysicalExpansion
