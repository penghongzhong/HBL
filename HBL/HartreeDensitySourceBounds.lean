import HBL.HartreePhysicalLinearization

/-!
# Actual Hartree density source estimates

Derive all three convolution-integrability hypotheses in the physical Taylor
expansion from function-space bounds. The real background needs L4 and
L-infinity control, not L2. The complex perturbation needs L2 and L-infinity.
The quadratic density potential is bounded by the square of the perturbation
size. These are native estimates, not fields of a local-theory structure.
No constrained propagator, derivative estimate or main blow-up conclusion
is asserted here.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
namespace HBL.RegularRadiation.PhysicalExpansion

/-- Coefficient in the quadratic quartic-density remainder bound. -/
def densityQuadraticConstant (M r : ℝ) : ℝ := 2 * M ^ 2 + (2 * M + r) ^ 2

private theorem density_linear_norm (a : ℝ) (z : ℂ) :
    ‖((4 * a ^ 3 * z.re : ℝ) : ℂ)‖ = 4 * |a| ^ 3 * |z.re| := by
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]

private theorem density_linear_domination {a M : ℝ} (z : ℂ)
    (hM : 0 ≤ M) (ha : |a| ≤ M) :
    ‖((4 * a ^ 3 * z.re : ℝ) : ℂ)‖ ≤
      (2 * M) * (|a| ^ 4 + ‖z‖ ^ 2) := by
  rw [density_linear_norm]
  calc
    _ ≤ 4 * |a| ^ 3 * ‖z‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (by positivity)
    _ = (2 * |a|) * (2 * (|a| ^ 2 * ‖z‖)) := by ring
    _ ≤ (2 * M) * (|a| ^ 4 + ‖z‖ ^ 2) := by
      apply mul_le_mul
      · linarith
      · nlinarith only [sq_nonneg (|a| ^ 2 - ‖z‖)]
      · positivity
      · positivity

private theorem density_remainder_domination {a M r : ℝ} (z : ℂ)
    (hM : 0 ≤ M) (hr : 0 ≤ r) (ha : |a| ≤ M) (hz : ‖z‖ ≤ r) :
    ‖((2 * a ^ 2 * ‖z‖ ^ 2 +
      (2 * a * z.re + ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ)‖ ≤
      densityQuadraticConstant M r * ‖z‖ ^ 2 := by
  have ha2 : a ^ 2 ≤ M ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg a) ha 2
    simpa only [sq_abs] using h
  have he : |2 * a * z.re + ‖z‖ ^ 2| ≤ (2 * M + r) * ‖z‖ := by
    calc
      _ ≤ |2 * a * z.re| + |‖z‖ ^ 2| := abs_add_le _ _
      _ = 2 * |a| * |z.re| + ‖z‖ ^ 2 := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (sq_nonneg ‖z‖)]
      _ ≤ 2 * M * ‖z‖ + r * ‖z‖ := by
        apply add_le_add
        · exact mul_le_mul (by linarith : 2 * |a| ≤ 2 * M)
            (Complex.abs_re_le_norm z) (abs_nonneg _) (by positivity)
        · nlinarith only [mul_le_mul_of_nonneg_right hz (norm_nonneg z)]
      _ = _ := by ring
  have he2 := pow_le_pow_left₀ (abs_nonneg (2 * a * z.re + ‖z‖ ^ 2)) he 2
  simp only [sq_abs, mul_pow] at he2
  have hnon : 0 ≤ 2 * a ^ 2 * ‖z‖ ^ 2 + (2 * a * z.re + ‖z‖ ^ 2) ^ 2 := by
    positivity
  rw [Complex.norm_real, Real.norm_of_nonneg hnon]
  unfold densityQuadraticConstant
  nlinarith only [he2, mul_le_mul_of_nonneg_right ha2 (sq_nonneg ‖z‖)]

/-- The first-order quartic density is integrable and its actual convolution
is absolutely convergent. No convolution-integrability input is used. -/
theorem densityLinear_source_integrable
    (w : Space → ℝ) (h : Space → ℂ)
    (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4)) (hh : MemLp h 2)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r) :
    Integrable (densityLinear w h) ∧
    ∀ x : Space, Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) * densityLinear w h y) := by
  have hre := Complex.continuous_re.comp_aestronglyMeasurable hh.aestronglyMeasurable
  have hm : AEStronglyMeasurable (densityLinear w h) := by
    unfold densityLinear
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (((hw.pow 3).const_mul 4).mul hre)
  have hdom : ∀ᵐ y, ‖densityLinear w h y‖ ≤
      (2 * M) * (|w y| ^ 4 + ‖h y‖ ^ 2) := by
    filter_upwards [hwb] with y hy
    exact density_linear_domination (h y) hM hy
  have hi : Integrable (densityLinear w h) :=
    ((hw4.add hh.norm.integrable_sq).const_mul (2 * M)).mono' hm hdom
  refine ⟨hi, ?_⟩
  intro x
  apply (potential_bound (densityLinear w h) hi (4 * M ^ 3 * r)
    (by positivity) ?_ x).1
  filter_upwards [hwb, hhb] with y hy hhy
  unfold densityLinear
  rw [density_linear_norm]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy 3) (by norm_num))
    ((Complex.abs_re_le_norm (h y)).trans hhy) (abs_nonneg _) (by positivity)

/-- The actual quadratic density potential has its natural L2--L-infinity
bound. In particular the density and every translated convolution are
integrable; these conclusions are derived before integral additivity is used. -/
theorem densityRemainder_source_bound
    (w : Space → ℝ) (h : Space → ℂ)
    (hw : AEStronglyMeasurable w) (hh : MemLp h 2)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r) :
    Integrable (densityRemainder w h) ∧
    ∀ x : Space,
      Integrable (fun y : Space => (kernel (x - y) : ℂ) * densityRemainder w h y) ∧
      ‖potential (densityRemainder w h) x‖ ≤
        densityQuadraticConstant M r *
          (nearMass * r ^ 2 + ∫ y : Space, ‖h y‖ ^ 2) := by
  have hA : 0 ≤ densityQuadraticConstant M r := by
    unfold densityQuadraticConstant
    positivity
  have hre := Complex.continuous_re.comp_aestronglyMeasurable hh.aestronglyMeasurable
  have h2 := hh.aestronglyMeasurable.norm.pow 2
  have hm : AEStronglyMeasurable (densityRemainder w h) := by
    unfold densityRemainder
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((((hw.pow 2).const_mul 2).mul h2).add
        ((((hw.const_mul 2).mul hre).add h2).pow 2))
  have hdom : ∀ᵐ y, ‖densityRemainder w h y‖ ≤
      densityQuadraticConstant M r * ‖h y‖ ^ 2 := by
    filter_upwards [hwb, hhb] with y hy hhy
    exact density_remainder_domination (h y) hM hr hy hhy
  have hi : Integrable (densityRemainder w h) :=
    (hh.norm.integrable_sq.const_mul (densityQuadraticConstant M r)).mono' hm hdom
  have hI : (∫ y : Space, ‖densityRemainder w h y‖) ≤
      densityQuadraticConstant M r * (∫ y : Space, ‖h y‖ ^ 2) := by
    have ht := integral_mono_ae hi.norm
      (hh.norm.integrable_sq.const_mul (densityQuadraticConstant M r)) hdom
    rwa [integral_const_mul] at ht
  have hb : ∀ᵐ y, ‖densityRemainder w h y‖ ≤ densityQuadraticConstant M r * r ^ 2 := by
    filter_upwards [hdom, hhb] with y hy hhy
    exact hy.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hhy 2) hA)
  refine ⟨hi, ?_⟩
  intro x
  have hP := potential_bound (densityRemainder w h) hi
    (densityQuadraticConstant M r * r ^ 2) (by positivity) hb x
  refine ⟨hP.1, ?_⟩
  calc
    _ ≤ nearMass * (densityQuadraticConstant M r * r ^ 2) +
        densityQuadraticConstant M r * (∫ y : Space, ‖h y‖ ^ 2) :=
      hP.2.trans (add_le_add_left hI _)
    _ = _ := by ring

/-- Quadratic small-ball control of the actual nonlocal density remainder. -/
theorem densityRemainder_small_ball_bound
    (w : Space → ℝ) (h : Space → ℂ)
    (hw : AEStronglyMeasurable w) (hh : MemLp h 2)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r)
    (hE : (∫ y : Space, ‖h y‖ ^ 2) ≤ r ^ 2) (x : Space) :
    ‖potential (densityRemainder w h) x‖ ≤
      densityQuadraticConstant M r * (nearMass + 1) * r ^ 2 := by
  have hA : 0 ≤ densityQuadraticConstant M r := by
    unfold densityQuadraticConstant
    positivity
  calc
    _ ≤ densityQuadraticConstant M r *
        (nearMass * r ^ 2 + ∫ y : Space, ‖h y‖ ^ 2) :=
      ((densityRemainder_source_bound w h hw hh hM hr hwb hhb).2 x).2
    _ ≤ densityQuadraticConstant M r * (nearMass * r ^ 2 + r ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hE _) hA
    _ = _ := by ring

/-- The exact physical Hartree expansion with all three convolution
integrability conditions discharged from function-space bounds. The
background is not required to lie in L2. -/
theorem physical_hartree_expansion_from_function_bounds
    (κ : ℝ) (w : Space → ℝ) (h : Space → ℂ)
    (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4)) (hh : MemLp h 2)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r)
    (x : Space) :
    Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) * quarticDensity (fun v => (w v : ℂ)) y) ∧
    Integrable (fun y : Space => (kernel (x - y) : ℂ) * densityLinear w h y) ∧
    Integrable (fun y : Space => (kernel (x - y) : ℂ) * densityRemainder w h y) ∧
    hartreeNonlinearity κ (fun y => (w y : ℂ) + h y) x =
      hartreeNonlinearity κ (fun y => (w y : ℂ)) x +
        linearTerm κ w h x + remainder κ w h x := by
  have hbase : Integrable (quarticDensity (fun y => (w y : ℂ))) := by
    simpa only [quarticDensity, Complex.norm_real, Real.norm_eq_abs] using hw4.ofReal
  have hb : ∀ᵐ y, ‖quarticDensity (fun v => (w v : ℂ)) y‖ ≤ M ^ 4 := by
    filter_upwards [hwb] with y hy
    simpa only [quarticDensity, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (abs_nonneg (w y)) 4)] using
      pow_le_pow_left₀ (abs_nonneg (w y)) hy 4
  have h0 := (potential_bound _ hbase (M ^ 4) (by positivity) hb x).1
  have h1 := (densityLinear_source_integrable w h hw hw4 hh hM hr hwb hhb).2 x
  have hR := ((densityRemainder_source_bound w h hw hh hM hr hwb hhb).2 x).1
  exact ⟨h0, h1, hR, physical_hartree_expansion κ w h x h0 h1 hR⟩

end HBL.RegularRadiation.PhysicalExpansion
