import HBL.WeightedFreeGreenSpectrum
import HBL.WeightedGreenSineModes
import Mathlib.Tactic.Lift

/-!
Classification of the positive eigenpairs of the actual weighted free
Green operator. The proved outgoing boundary condition quantizes the ODE
frequency, and the canonical integral representative identifies each
eigenvector with a scalar multiple of the actual radial L2 sine mode.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem greenFrequency_sineValue (n : ℕ) :
    greenFrequency (1 / (4 * (n : ℝ) ^ 2 - 1)) = 2 * (n : ℝ) := by
  unfold greenFrequency
  rw [one_div, inv_inv]
  have hpoly : 1 + (4 * (n : ℝ) ^ 2 - 1) = (2 * (n : ℝ)) ^ 2 := by ring
  rw [hpoly, Real.sqrt_sq (by positivity)]

private theorem weightedGreenDecay_mul_oscillation (n : ℕ) (r : ℝ) :
    weightedGreenDecay r * greenOscillation (2 * (n : ℝ)) r =
      weightedHartreeSineMode n r := by
  have hs : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hd : 1 + r ^ 2 ≠ 0 := by positivity
  have hweight : weightedGreenDecay r * Real.sqrt (1 + r ^ 2) = bubble r := by
    unfold weightedGreenDecay bubble
    field_simp [hs, hd]
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + r ^ 2 by positivity)]
  unfold greenOscillation weightedHartreeSineMode
  rw [← mul_assoc, hweight]

private theorem weightedFreeGreen_eigen_mem_sine_span_of_frequency
    {mu : ℝ} (hmu : 0 < mu) (f : RealL2 halfLineMeasure)
    (heig : weightedFreeGreenOperator f = mu • f)
    (n : ℕ) (hfrequency : greenFrequency mu = 2 * (n : ℝ)) :
    f ∈ Submodule.span ℝ {weightedHartreeSineModeL2 n} := by
  obtain ⟨c, hstate⟩ := weightedGreenEigen_state_eq_oscillation hmu f heig
  have hq (r : ℝ) (hr : 0 ≤ r) :
      weightedGreenPrimitive f r = c * greenOscillation (2 * (n : ℝ)) r := by
    have hs := congrArg Prod.fst (hstate r hr)
    change halfLineMinGreen (weightedGreenEigenSource mu f) r =
      c * greenOscillation (greenFrequency mu) r at hs
    rw [← congrFun (weightedGreenPrimitive_eq_eigen_minGreen hmu.ne' f heig) r,
      hfrequency] at hs
    exact hs
  refine Submodule.mem_span_singleton.mpr ⟨mu⁻¹ * c, ?_⟩
  apply Lp.ext
  have hpoint := weightedFreeGreenOperator_ae_pointwise f
  rw [heig] at hpoint
  filter_upwards [hpoint, Lp.coeFn_smul mu f,
      Lp.coeFn_smul (mu⁻¹ * c) (weightedHartreeSineModeL2 n),
      weightedHartreeSineModeL2_ae n,
      ae_restrict_mem measurableSet_Ioi]
      with r hpoint hsmall hlarge hmode hr
  rw [hsmall] at hpoint
  simp only [Pi.smul_apply, smul_eq_mul] at hpoint
  rw [hlarge]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hmode]
  unfold weightedFreeGreenPointwise at hpoint
  rw [hq r hr.le] at hpoint
  have hscalar : mu * f r = c * weightedHartreeSineMode n r := by
    calc
      mu * f r = weightedGreenDecay r *
          (c * greenOscillation (2 * (n : ℝ)) r) := hpoint
      _ = c * (weightedGreenDecay r * greenOscillation (2 * (n : ℝ)) r) := by ring
      _ = c * weightedHartreeSineMode n r := by
        rw [weightedGreenDecay_mul_oscillation]
  calc
    (mu⁻¹ * c) * weightedHartreeSineMode n r =
        mu⁻¹ * (c * weightedHartreeSineMode n r) := by ring
    _ = mu⁻¹ * (mu * f r) := by rw [hscalar]
    _ = f r := by rw [← mul_assoc, inv_mul_cancel₀ hmu.ne', one_mul]

/-- Every positive eigenvalue of the actual Green operator is quantized
by a positive integer, using its proved outgoing ODE boundary condition. -/
theorem weightedFreeGreen_positive_eigenvalue_quantized
    {mu : ℝ} (hmu : 0 < mu) (f : RealL2 halfLineMeasure) (hf : f ≠ 0)
    (heig : weightedFreeGreenOperator f = mu • f) :
    ∃ n : ℕ, 0 < n ∧ mu = 1 / (4 * (n : ℝ) ^ 2 - 1) := by
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp
    (weightedGreenEigen_frequency_sin_eq_zero hmu f hf heig)
  have hfrequency : greenFrequency mu = 2 * (k : ℝ) := by
    apply mul_right_cancel₀ Real.pi_ne_zero
    calc
      greenFrequency mu * Real.pi = 2 * ((k : ℝ) * Real.pi) := by
        nlinarith [hk]
      _ = (2 * (k : ℝ)) * Real.pi := by ring
  have hkreal : 0 < (k : ℝ) := by
    nlinarith [greenFrequency_pos hmu]
  have hkint : (0 : ℤ) < k := by exact_mod_cast hkreal
  lift k to ℕ using hkint.le
  push_cast at hfrequency
  have hknat : 0 < k := by exact_mod_cast hkint
  refine ⟨k, hknat, ?_⟩
  have hinv : mu⁻¹ = 4 * (k : ℝ) ^ 2 - 1 := by
    have hs := greenFrequency_sq_sub_one hmu
    rw [hfrequency] at hs
    nlinarith
  calc
    mu = (mu⁻¹)⁻¹ := (inv_inv mu).symm
    _ = 1 / (4 * (k : ℝ) ^ 2 - 1) := by rw [hinv, one_div]

/-- Every positive nonzero Green eigenpair has the quantized eigenvalue
and a vector in the corresponding actual one-dimensional sine span. -/
theorem weightedFreeGreen_positive_eigen_classification
    {mu : ℝ} (hmu : 0 < mu) (f : RealL2 halfLineMeasure) (hf : f ≠ 0)
    (heig : weightedFreeGreenOperator f = mu • f) :
    ∃ n : ℕ, 0 < n ∧ mu = 1 / (4 * (n : ℝ) ^ 2 - 1) ∧
      f ∈ Submodule.span ℝ {weightedHartreeSineModeL2 n} := by
  obtain ⟨n, hn, hvalue⟩ :=
    weightedFreeGreen_positive_eigenvalue_quantized hmu f hf heig
  refine ⟨n, hn, hvalue, ?_⟩
  apply weightedFreeGreen_eigen_mem_sine_span_of_frequency hmu f heig n
  rw [hvalue, greenFrequency_sineValue]

/-- Exact eigenspace classification at each positive-integer Green
eigenvalue, including the zero vector on both sides. -/
theorem weightedFreeGreen_sine_eigen_iff (n : ℕ) (hn : 0 < n)
    (f : RealL2 halfLineMeasure) :
    weightedFreeGreenOperator f = (1 / (4 * (n : ℝ) ^ 2 - 1)) • f ↔
      f ∈ Submodule.span ℝ {weightedHartreeSineModeL2 n} := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmu : 0 < 1 / (4 * (n : ℝ) ^ 2 - 1) := by
    apply one_div_pos.mpr
    nlinarith
  constructor
  · intro heig
    exact weightedFreeGreen_eigen_mem_sine_span_of_frequency hmu f heig n
      (greenFrequency_sineValue n)
  · intro hf
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
    rw [map_smul, weightedFreeGreenOperator_sineMode n hn]
    module

end HBL.Modulation.Monopole
