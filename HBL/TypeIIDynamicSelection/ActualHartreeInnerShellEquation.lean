import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedInnerClassical
import HBL.InnerEstimates.PlusOutputBound
import HBL.InnerEstimates.PlusRemainderDifference
import HBL.InnerEstimates.MinusRemainderDifference
import HBL.InnerDerivatives.PlusDerivativeBound
import HBL.InnerDerivatives.MinusDerivativeBound
import HBL.InnerDerivatives.AffineDerivativeFar
import HBL.WeightedHartreePointwiseContinuous
import HBL.KummerFrozenAnnulus
import Mathlib.Tactic

/-!
The actual normalized Fredholm outputs on the matching shell.

The constants below depend only on the fixed inverse, its forced affine
charge and the original source space L^{2,7/4}.  The physical quotients
of the SAME outputs satisfy a source-norm bound for the difference
between their full bubble Hessian equation and the radial Laplace
equation.  That difference is O(N/r^4), not the large commutator of a
bare cutoff.  In particular a matched exterior propagation must retain
the same forcing F/r, or start beyond its support.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

/-- One fixed bound for both physical values. -/
def actualInnerShellValueConstant : ℝ :=
  |innerPlusRemainderConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)| +
  |innerMinusRemainderConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)| +
  2 * ‖weightedSourceResonanceL2 (7 / 4 : ℝ) (by norm_num)‖ +
  ‖weightedPhaseSourceResonanceL2 (7 / 4 : ℝ) (by norm_num)‖

/-- The affine slope cancels from the physical derivative. -/
def actualInnerShellDerivativeConstant : ℝ :=
  |innerPlusDerivativeConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)| +
  |innerMinusDerivativeConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)| +
  |innerPlusRemainderConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)| +
  |innerMinusRemainderConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)|

/-- A source-independent bound for the true bubble-Hessian/Laplace gap. -/
def actualInnerShellEquationConstant : ℝ :=
  9 * actualInnerShellValueConstant +
  Real.sqrt (288 * Real.pi) *
    |innerPlusOutputConstant (7 / 4 : ℝ) 2
      (by norm_num) (by norm_num) (by norm_num)|

private theorem actual_inner_shell_constants_nonneg :
    0 ≤ actualInnerShellValueConstant ∧
    0 ≤ actualInnerShellDerivativeConstant ∧
    0 ≤ actualInnerShellEquationConstant := by
  have hv : 0 ≤ actualInnerShellValueConstant := by
    unfold actualInnerShellValueConstant
    positivity
  have hd : 0 ≤ actualInnerShellDerivativeConstant := by
    unfold actualInnerShellDerivativeConstant
    positivity
  refine ⟨hv, hd, ?_⟩
  unfold actualInnerShellEquationConstant
  positivity

private theorem actual_inner_affine_physical_jet_bound
    (p : ℝ → ℝ) (alpha A B D N r : ℝ)
    (hA : 0 ≤ A) (hN : 0 ≤ N) (hr : 2 < r)
    (hp : DifferentiableAt ℝ p r)
    (hp0 : |p r| ≤ A * N) (ha : |alpha| ≤ B * N)
    (hp1 : (1 + r) * |deriv p r| ≤ D * N) :
    |affineRestore p alpha r / r| ≤ (A + B) * N ∧
    r ^ 2 * |deriv (fun x => affineRestore p alpha x / x) r| ≤
      (D + A) * N := by
  have hr0 : 0 < r := by linarith
  have hq : DifferentiableAt ℝ (affineRestore p alpha) r := by
    exact hp.add ((model_hasDerivAt_one_of_two_lt r hr).differentiableAt.const_mul alpha)
  have hv : |affineRestore p alpha r| ≤ (A + B) * N * r := by
    change |p r + alpha * model r| ≤ _
    rw [model_eq_id_of_two_le r hr.le]
    calc
      |p r + alpha * r| ≤ |p r| + |alpha * r| := abs_add_le _ _
      _ ≤ A * N + (B * N) * r := by
        rw [abs_mul, abs_of_pos hr0]
        exact add_le_add hp0 (mul_le_mul_of_nonneg_right ha hr0.le)
      _ ≤ (A * N) * r + (B * N) * r := by
        exact add_le_add
          (le_mul_of_one_le_right (mul_nonneg hA hN) (by linarith)) le_rfl
      _ = (A + B) * N * r := by ring
  have he : deriv (fun x => affineRestore p alpha x / x) r =
      (deriv p r * r - p r) / r ^ 2 := by
    rw [(div_radius_hasDerivAt (affineRestore p alpha) hr0 hq).deriv,
      affineRestore_deriv_far p alpha hr hp]
    unfold affineRestore
    rw [model_eq_id_of_two_le r hr.le]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · rw [abs_div, abs_of_pos hr0]
    exact (div_le_iff₀ hr0).2 hv
  · rw [he, abs_div, abs_of_pos (pow_pos hr0 2)]
    have he' : r ^ 2 * (|deriv p r * r - p r| / r ^ 2) =
        |deriv p r * r - p r| := by
      field_simp [hr0.ne']
    rw [he']
    have hp1' : |deriv p r| * r ≤ D * N := by
      nlinarith [abs_nonneg (deriv p r)]
    calc
      |deriv p r * r - p r| ≤ |deriv p r * r| + |p r| := abs_sub_le _ _
      _ ≤ D * N + A * N := by
        rw [abs_mul, abs_of_pos hr0]
        exact add_le_add hp1' hp0
      _ = (D + A) * N := by ring

private theorem actual_inner_normalized_physical_jets
    (F : ℝ → ℝ) (hF : InWeightedL2 (7 / 4 : ℝ) F)
    (hcF : Continuous F) (r : ℝ) (hr : 2 < r) :
    let qp := normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
    let qm := normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
    let N := innerWeightedNorm (7 / 4 : ℝ) F
    (|qp r / r| ≤ actualInnerShellValueConstant * N ∧
      r ^ 2 * |deriv (fun x => qp x / x) r| ≤ actualInnerShellDerivativeConstant * N) ∧
    (|qm r / r| ≤ actualInnerShellValueConstant * N ∧
      r ^ 2 * |deriv (fun x => qm x / x) r| ≤ actualInnerShellDerivativeConstant * N) := by
  let Ap := innerPlusRemainderConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)
  let Am := innerMinusRemainderConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)
  let Bp := 2 * ‖weightedSourceResonanceL2 (7 / 4 : ℝ) (by norm_num)‖
  let Bm := ‖weightedPhaseSourceResonanceL2 (7 / 4 : ℝ) (by norm_num)‖
  let Dp := innerPlusDerivativeConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)
  let Dm := innerMinusDerivativeConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)
  let N := innerWeightedNorm (7 / 4 : ℝ) F
  have hN : 0 ≤ N := innerWeightedNorm_nonneg _ _
  have hr0 : 0 < r := by linarith
  have h0 : InWeightedL2 (7 / 4 : ℝ) (fun _ => 0) := by simp [InWeightedL2]
  have hzero := normalizedRemainder_zero (7 / 4 : ℝ) (by norm_num) (by norm_num) h0
  have hp0 := normalizedPlusRemainder_difference_le
    (7 / 4 : ℝ) (by norm_num) (by norm_num) F (fun _ => 0) hF h0 hr0
  have hm0 := normalizedMinusRemainder_difference_le
    (7 / 4 : ℝ) (by norm_num) (by norm_num) F (fun _ => 0) hF h0 hr0
  rw [hzero.1, innerWeightedData_zero] at hp0
  rw [hzero.2, innerWeightedData_zero] at hm0
  have hp0' : |normalizedPlusRemainder (7 / 4 : ℝ)
      (by norm_num) (by norm_num) F hF r| ≤ |Ap| * N := by
    have hh : |normalizedPlusRemainder (7 / 4 : ℝ)
        (by norm_num) (by norm_num) F hF r| ≤ Ap * N := by
      simpa only [sub_zero, Real.norm_eq_abs, ← innerWeightedNorm_eq] using hp0
    exact hh.trans (mul_le_mul_of_nonneg_right (le_abs_self Ap) hN)
  have hm0' : |normalizedMinusRemainder (7 / 4 : ℝ)
      (by norm_num) (by norm_num) F hF r| ≤ |Am| * N := by
    have hh : |normalizedMinusRemainder (7 / 4 : ℝ)
        (by norm_num) (by norm_num) F hF r| ≤ Am * N := by
      simpa only [sub_zero, Real.norm_eq_abs, ← innerWeightedNorm_eq] using hm0
    exact hh.trans (mul_le_mul_of_nonneg_right (le_abs_self Am) hN)
  have hap := actualPlusCharge_difference_le (7 / 4 : ℝ) (by norm_num)
    F (fun _ => 0) hF h0
  have ham := actualMinusCharge_difference_le (7 / 4 : ℝ) (by norm_num)
    F (fun _ => 0) hF h0
  have hzp : actualPlusCharge (fun _ => 0) = 0 := by simp [actualPlusCharge, channelPairing]
  have hzm : actualMinusCharge (fun _ => 0) = 0 := by simp [actualMinusCharge, channelPairing]
  rw [hzp, innerWeightedData_zero] at hap
  rw [hzm, innerWeightedData_zero] at ham
  have hap' : |actualPlusCharge F| ≤ Bp * N := by
    simpa only [sub_zero, Real.norm_eq_abs, ← innerWeightedNorm_eq] using hap
  have ham' : |actualMinusCharge F| ≤ Bm * N := by
    simpa only [sub_zero, Real.norm_eq_abs, ← innerWeightedNorm_eq] using ham
  have hdp := normalizedPlusRemainder_derivative_bound
    (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF hcF hr0
  have hdm := normalizedMinusRemainder_derivative_bound
    (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF hcF hr0
  have hdp' : (1 + r) * |deriv (normalizedPlusRemainder (7 / 4 : ℝ)
      (by norm_num) (by norm_num) F hF) r| ≤ |Dp| * N := by
    have hh : (1 + r) * |deriv (normalizedPlusRemainder (7 / 4 : ℝ)
        (by norm_num) (by norm_num) F hF) r| ≤ Dp * N := by
      simpa only [Real.norm_eq_abs] using hdp
    exact hh.trans (mul_le_mul_of_nonneg_right (le_abs_self Dp) hN)
  have hdm' : (1 + r) * |deriv (normalizedMinusRemainder (7 / 4 : ℝ)
      (by norm_num) (by norm_num) F hF) r| ≤ |Dm| * N := by
    have hh : (1 + r) * |deriv (normalizedMinusRemainder (7 / 4 : ℝ)
        (by norm_num) (by norm_num) F hF) r| ≤ Dm * N := by
      simpa only [Real.norm_eq_abs] using hdm
    exact hh.trans (mul_le_mul_of_nonneg_right (le_abs_self Dm) hN)
  have hjp := actual_inner_affine_physical_jet_bound
    (normalizedPlusRemainder (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF)
    (actualPlusCharge F) |Ap| Bp |Dp| N r (abs_nonneg _) hN hr
    (normalizedPlusRemainder_hasDerivAt (7 / 4 : ℝ) (by norm_num) (by norm_num)
      F hF hcF hr0).differentiableAt hp0' hap' hdp'
  have hjm := actual_inner_affine_physical_jet_bound
    (normalizedMinusRemainder (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF)
    (actualMinusCharge F) |Am| Bm |Dm| N r (abs_nonneg _) hN hr
    (normalizedMinusRemainder_hasDerivAt (7 / 4 : ℝ) (by norm_num) (by norm_num)
      F hF hcF hr0).differentiableAt hm0' ham' hdm'
  have hvp : |Ap| + Bp ≤ actualInnerShellValueConstant := by
    change |Ap| + Bp ≤ |Ap| + |Am| + Bp + Bm
    have hb : 0 ≤ Bm := norm_nonneg _
    linarith [abs_nonneg Am]
  have hvm : |Am| + Bm ≤ actualInnerShellValueConstant := by
    change |Am| + Bm ≤ |Ap| + |Am| + Bp + Bm
    have hb : 0 ≤ Bp := by dsimp [Bp]; positivity
    linarith [abs_nonneg Ap]
  have hdpC : |Dp| + |Ap| ≤ actualInnerShellDerivativeConstant := by
    change |Dp| + |Ap| ≤ |Dp| + |Dm| + |Ap| + |Am|
    linarith [abs_nonneg Dm, abs_nonneg Am]
  have hdmC : |Dm| + |Am| ≤ actualInnerShellDerivativeConstant := by
    change |Dm| + |Am| ≤ |Dp| + |Dm| + |Ap| + |Am|
    linarith [abs_nonneg Dp, abs_nonneg Ap]
  exact ⟨⟨hjp.1.trans (mul_le_mul_of_nonneg_right hvp hN),
      hjp.2.trans (mul_le_mul_of_nonneg_right hdpC hN)⟩,
    ⟨hjm.1.trans (mul_le_mul_of_nonneg_right hvm hN),
      hjm.2.trans (mul_le_mul_of_nonneg_right hdmC hN)⟩⟩

/-- The genuine Hartree kernel row gives a pointwise estimate, including
the observation radius. No null-set choice enters the shell ODE. -/
private theorem actual_inner_nonlocal_pointwise_bound
    (q : ℝ → ℝ)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure)
    (r : ℝ) (hr : 0 < r) :
    |nonlocalApply q r| ≤ Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
      ‖hq.toLp (fun rho => weightedGreenDecay rho * q rho)‖ := by
  let x : RealL2 halfLineMeasure := hq.toLp (fun rho => weightedGreenDecay rho * q rho)
  let s : Ici (0 : ℝ) := ⟨r, hr.le⟩
  have hrowSq : ‖weightedHartreeRow s‖ ^ 2 = 576 * weightedZeroGreen r r := by
    rw [← real_inner_self_eq_norm_sq, weightedHartreeRow_inner]
  have hrowBound : ‖weightedHartreeRow s‖ ≤ Real.sqrt (288 * Real.pi) * bubble r := by
    have hsq : ‖weightedHartreeRow s‖ ^ 2 ≤
        (Real.sqrt (288 * Real.pi) * bubble r) ^ 2 := by
      rw [hrowSq]
      have hd := weightedZeroGreen_diag_le hr
      have hs := Real.sq_sqrt (show 0 ≤ 288 * Real.pi by positivity)
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (bubble_nonneg r))).mp hsq
  have hp : |weightedHartreePointwise x r| ≤
      Real.sqrt (288 * Real.pi) * bubble r * ‖x‖ := by
    rw [show weightedHartreePointwise x r = inner ℝ (weightedHartreeRow s) x from
      weightedHartreePointwise_eq_inner x s]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hrowBound (norm_nonneg x))
  have he : |nonlocalApply q r| =
      (1 + r ^ 2)⁻¹ * |weightedHartreePointwise x r| := by
    rw [weightedHartreePointwise_conjugation,
      abs_mul, abs_of_pos (show 0 < 1 + r ^ 2 by positivity)]
    field_simp
  rw [he]
  calc
    (1 + r ^ 2)⁻¹ * |weightedHartreePointwise x r| ≤
        (1 + r ^ 2)⁻¹ * (Real.sqrt (288 * Real.pi) * bubble r * ‖x‖) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = Real.sqrt (288 * Real.pi) * bubble r ^ 3 * ‖x‖ := by
      rw [← bubble_sq]
      ring

private theorem actual_inner_normalized_plus_nonlocal_bound
    (F : ℝ → ℝ) (hF : InWeightedL2 (7 / 4 : ℝ) F)
    (r : ℝ) (hr : 0 < r) :
    let q := normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
    |nonlocalApply q r| ≤
      (Real.sqrt (288 * Real.pi) *
        |innerPlusOutputConstant (7 / 4 : ℝ) 2
          (by norm_num) (by norm_num) (by norm_num)|) *
      innerWeightedNorm (7 / 4 : ℝ) F * bubble r ^ 3 := by
  let q := normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
  have hqw : InWeightedL2 (-(2 : ℝ)) q :=
    (normalizedPlusOutput_properties (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF).2.2.1
      2 (by norm_num)
  have hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure := by
    simpa [InWeightedL2, affineJapaneseWeight, weightedGreenDecay, Real.rpow_neg_one] using hqw
  have hn : ‖hq.toLp (fun r => weightedGreenDecay r * q r)‖ =
      innerWeightedNorm (-(2 : ℝ)) q := by
    simpa [innerWeightedNorm, affineJapaneseWeight, weightedGreenDecay,
      Real.rpow_neg_one] using (Lp.norm_toLp _ hq)
  have hnb := normalizedPlusOutput_weighted_norm_le
    (7 / 4 : ℝ) 2 (by norm_num) (by norm_num) (by norm_num) F hF
  have hnb' : ‖hq.toLp (fun r => weightedGreenDecay r * q r)‖ ≤
      |innerPlusOutputConstant (7 / 4 : ℝ) 2
        (by norm_num) (by norm_num) (by norm_num)| * innerWeightedNorm (7 / 4 : ℝ) F := by
    rw [hn]
    exact hnb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (innerWeightedNorm_nonneg _ _))
  calc
    |nonlocalApply q r| ≤ Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
        ‖hq.toLp (fun rho => weightedGreenDecay rho * q rho)‖ :=
      actual_inner_nonlocal_pointwise_bound q hq r hr
    _ ≤ Real.sqrt (288 * Real.pi) * bubble r ^ 3 *
        (|innerPlusOutputConstant (7 / 4 : ℝ) 2
          (by norm_num) (by norm_num) (by norm_num)| * innerWeightedNorm (7 / 4 : ℝ) F) :=
      mul_le_mul_of_nonneg_left hnb' (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (bubble_nonneg r) _))
    _ = _ := by ring

private theorem actual_inner_bubble_inverse_radius
    (r : ℝ) (hr : 0 < r) :
    bubble r ^ 4 ≤ 1 / r ^ 4 ∧ bubble r ^ 3 / r ≤ 1 / r ^ 4 := by
  have hb : bubble r ≤ 1 / r := (le_div_iff₀ hr).2 (by
    simpa only [mul_comm] using radius_mul_bubble_le_one hr.le)
  have hb0 := bubble_nonneg r
  constructor
  · calc
      bubble r ^ 4 ≤ (1 / r) ^ 4 := by gcongr
      _ = 1 / r ^ 4 := by rw [div_pow, one_pow]
  · calc
      bubble r ^ 3 / r ≤ (1 / r) ^ 3 / r := by gcongr
      _ = 1 / r ^ 4 := by field_simp

/-- Same normalized outputs, same original weighted source norm, and a
uniform shell ODE gap. The forcing F/r is retained explicitly, so no
smallness of an arbitrary shell source is silently assumed. -/
theorem actual_Hartree_normalized_inner_shell_equation_bound
    (F : ℝ → ℝ) (hF : InWeightedL2 (7 / 4 : ℝ) F)
    (hcF : Continuous F) (R r : ℝ) (hR : 2 < R) (hr : R ≤ r) :
    let qp := normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
    let qm := normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
    let N := innerWeightedNorm (7 / 4 : ℝ) F
    (|qp r / r| ≤ actualInnerShellValueConstant * N ∧
      r ^ 2 * |deriv (fun x => qp x / x) r| ≤ actualInnerShellDerivativeConstant * N ∧
      |radialLaplacian (fun x => qp x / x) r + F r / r| ≤
        actualInnerShellEquationConstant * N / R ^ 4) ∧
    (|qm r / r| ≤ actualInnerShellValueConstant * N ∧
      r ^ 2 * |deriv (fun x => qm x / x) r| ≤ actualInnerShellDerivativeConstant * N ∧
      |radialLaplacian (fun x => qm x / x) r + F r / r| ≤
        actualInnerShellEquationConstant * N / R ^ 4) := by
  let qp := normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
  let qm := normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
  let N := innerWeightedNorm (7 / 4 : ℝ) F
  let C := Real.sqrt (288 * Real.pi) * |innerPlusOutputConstant (7 / 4 : ℝ) 2
    (by norm_num) (by norm_num) (by norm_num)|
  have hr2 : 2 < r := lt_of_lt_of_le hR hr
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := by linarith
  have hN : 0 ≤ N := innerWeightedNorm_nonneg _ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hv := actual_inner_normalized_physical_jets F hF hcF r hr2
  have hp := normalizedPlusOutput_classical (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF hcF
  have hm := normalizedMinusOutput_classical (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF hcF
  have hpot : potential r = 3 * bubble r ^ 4 := by
    unfold potential
    rw [show bubble r ^ 4 = (bubble r ^ 2) ^ 2 by ring, bubble_sq, inv_pow]
    ring
  have hep : radialLaplacian (fun x => qp x / x) r + F r / r =
      -(9 * bubble r ^ 4 * (qp r / r) + nonlocalApply qp r / r) := by
    rw [radialLaplacian_div_radius qp (fun x hx => (hp x hx).1) hr0 (hp r hr0).2.1]
    have he := (hp r hr0).2.2
    change -deriv (deriv qp) r - 3 * potential r * qp r - nonlocalApply qp r = F r at he
    rw [hpot] at he
    field_simp [hr0.ne']
    linarith
  have hem : radialLaplacian (fun x => qm x / x) r + F r / r =
      -(3 * bubble r ^ 4 * (qm r / r)) := by
    rw [radialLaplacian_div_radius qm (fun x hx => (hm x hx).1) hr0 (hm r hr0).2.1]
    have he := (hm r hr0).2.2
    change -deriv (deriv qm) r - potential r * qm r = F r at he
    rw [hpot] at he
    field_simp [hr0.ne']
    linarith
  have hb := actual_inner_bubble_inverse_radius r hr0
  have hV0 := actual_inner_shell_constants_nonneg.1
  have hE0 := actual_inner_shell_constants_nonneg.2.2
  have hnloc : |nonlocalApply qp r / r| ≤ C * N / r ^ 4 := by
    rw [abs_div, abs_of_pos hr0]
    have hn := actual_inner_normalized_plus_nonlocal_bound F hF r hr0
    calc
      |nonlocalApply qp r| / r ≤ (C * N * bubble r ^ 3) / r :=
        div_le_div_of_nonneg_right hn hr0.le
      _ = (C * N) * (bubble r ^ 3 / r) := by ring
      _ ≤ (C * N) * (1 / r ^ 4) := mul_le_mul_of_nonneg_left hb.2 (mul_nonneg hC hN)
      _ = C * N / r ^ 4 := by ring
  have hlocalp : |9 * bubble r ^ 4 * (qp r / r)| ≤
      9 * actualInnerShellValueConstant * N / r ^ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 9),
      abs_of_nonneg (pow_nonneg (bubble_nonneg r) _)]
    calc
      9 * bubble r ^ 4 * |qp r / r| ≤
          9 * bubble r ^ 4 * (actualInnerShellValueConstant * N) :=
        mul_le_mul_of_nonneg_left hv.1.1 (by positivity)
      _ ≤ 9 * (1 / r ^ 4) * (actualInnerShellValueConstant * N) := by
        gcongr
        exact hb.1
      _ = _ := by ring
  have hlocalm : |3 * bubble r ^ 4 * (qm r / r)| ≤
      9 * actualInnerShellValueConstant * N / r ^ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3),
      abs_of_nonneg (pow_nonneg (bubble_nonneg r) _)]
    calc
      3 * bubble r ^ 4 * |qm r / r| ≤
          3 * bubble r ^ 4 * (actualInnerShellValueConstant * N) :=
        mul_le_mul_of_nonneg_left hv.2.1 (by positivity)
      _ ≤ 9 * (1 / r ^ 4) * (actualInnerShellValueConstant * N) := by
        gcongr
        exact hb.1
      _ = _ := by ring
  have hrad : actualInnerShellEquationConstant * N / r ^ 4 ≤
      actualInnerShellEquationConstant * N / R ^ 4 := by
    apply div_le_div_of_nonneg_left (mul_nonneg hE0 hN) (pow_pos hR0 4)
    gcongr
  have hEp : |radialLaplacian (fun x => qp x / x) r + F r / r| ≤
      actualInnerShellEquationConstant * N / R ^ 4 := by
    apply le_trans ?_ hrad
    rw [hep, abs_neg]
    calc
      _ ≤ |9 * bubble r ^ 4 * (qp r / r)| + |nonlocalApply qp r / r| := abs_add_le _ _
      _ ≤ 9 * actualInnerShellValueConstant * N / r ^ 4 + C * N / r ^ 4 :=
        add_le_add hlocalp hnloc
      _ = _ := by dsimp [actualInnerShellEquationConstant, C]; ring
  have hEm : |radialLaplacian (fun x => qm x / x) r + F r / r| ≤
      actualInnerShellEquationConstant * N / R ^ 4 := by
    apply le_trans ?_ hrad
    rw [hem, abs_neg]
    exact hlocalm.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by
        change 9 * actualInnerShellValueConstant ≤ 9 * actualInnerShellValueConstant + C
        linarith) hN) (pow_nonneg hr0.le 4))
  exact ⟨⟨hv.1.1, hv.1.2, hEp⟩, ⟨hv.2.1, hv.2.2, hEm⟩⟩

/-- The original frozen Kummer operator, written in the inner radius
`r = a z`, applied to the same physical quotient. Its forcing is the
same `-F/r` as in the inner equation. -/
def actualInnerScaledKummerDefect
    (mu theta a : ℝ) (F q : ℝ → ℝ) (r : ℝ) : ℂ :=
  ((radialLaplacian (fun x => q x / x) r + F r / r : ℝ) : ℂ) +
    ((a ^ 2)⁻¹ : ℝ) •
      (Complex.I * (r : ℂ) / 2 *
          ((deriv (fun x => q x / x) r : ℝ) : ℂ) +
        frozenZeroCoeff mu theta * ((q r / r : ℝ) : ℂ))

def actualInnerShellKummerConstant (mu theta : ℝ) : ℝ :=
  actualInnerShellDerivativeConstant +
    ‖frozenZeroCoeff mu theta‖ * actualInnerShellValueConstant

private theorem actual_inner_scaled_Kummer_bound
    (mu theta a R r N : ℝ) (F q : ℝ → ℝ)
    (hr : 2 < r)
    (hv : |q r / r| ≤ actualInnerShellValueConstant * N)
    (hd : r ^ 2 * |deriv (fun x => q x / x) r| ≤
      actualInnerShellDerivativeConstant * N)
    (he : |radialLaplacian (fun x => q x / x) r + F r / r| ≤
      actualInnerShellEquationConstant * N / R ^ 4) :
    ‖actualInnerScaledKummerDefect mu theta a F q r‖ ≤
      actualInnerShellEquationConstant * N / R ^ 4 +
        actualInnerShellKummerConstant mu theta * N / a ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hd0 := abs_nonneg (deriv (fun x => q x / x) r)
  have hdrift : ‖Complex.I * (r : ℂ) / 2 *
      ((deriv (fun x => q x / x) r : ℝ) : ℂ)‖ ≤
        actualInnerShellDerivativeConstant * N := by
    have heq : ‖Complex.I * (r : ℂ) / 2 *
        ((deriv (fun x => q x / x) r : ℝ) : ℂ)‖ =
        (r / 2) * |deriv (fun x => q x / x) r| := by
      simp only [norm_mul, norm_div, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      norm_num
    rw [heq]
    have hrr : r / 2 ≤ r ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hrr hd0).trans hd
  have hzero : ‖frozenZeroCoeff mu theta * ((q r / r : ℝ) : ℂ)‖ ≤
      ‖frozenZeroCoeff mu theta‖ * (actualInnerShellValueConstant * N) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hv (norm_nonneg _)
  have hs : ‖Complex.I * (r : ℂ) / 2 *
        ((deriv (fun x => q x / x) r : ℝ) : ℂ) +
      frozenZeroCoeff mu theta * ((q r / r : ℝ) : ℂ)‖ ≤
        actualInnerShellKummerConstant mu theta * N := by
    calc
      _ ≤ ‖Complex.I * (r : ℂ) / 2 *
          ((deriv (fun x => q x / x) r : ℝ) : ℂ)‖ +
          ‖frozenZeroCoeff mu theta * ((q r / r : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ actualInnerShellDerivativeConstant * N +
          ‖frozenZeroCoeff mu theta‖ * (actualInnerShellValueConstant * N) :=
        add_le_add hdrift hzero
      _ = _ := by unfold actualInnerShellKummerConstant; ring
  unfold actualInnerScaledKummerDefect
  calc
    _ ≤ ‖((radialLaplacian (fun x => q x / x) r + F r / r : ℝ) : ℂ)‖ +
        ‖((a ^ 2)⁻¹ : ℝ) •
          (Complex.I * (r : ℂ) / 2 *
              ((deriv (fun x => q x / x) r : ℝ) : ℂ) +
            frozenZeroCoeff mu theta * ((q r / r : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ actualInnerShellEquationConstant * N / R ^ 4 +
        (a ^ 2)⁻¹ * (actualInnerShellKummerConstant mu theta * N) := by
      rw [Complex.norm_real, Real.norm_eq_abs, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg a))]
      exact add_le_add he (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (sq_nonneg a)))
    _ = _ := by ring

/-- A real source-norm relative estimate for the actual inner-field
Kummer defect: the bubble terms cost R^(-4) and the complete frozen
transport/zero-order terms cost a^(-2). Both normalized channels use
the same already constructed inverse and its forced affine tail. -/
theorem actual_Hartree_normalized_inner_scaled_Kummer_bound
    (mu theta a : ℝ) (F : ℝ → ℝ)
    (hF : InWeightedL2 (7 / 4 : ℝ) F) (hcF : Continuous F)
    (R r : ℝ) (hR : 2 < R) (hr : R ≤ r) :
    let qp := normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
    let qm := normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
    let N := innerWeightedNorm (7 / 4 : ℝ) F
    ‖actualInnerScaledKummerDefect mu theta a F qp r‖ ≤
      actualInnerShellEquationConstant * N / R ^ 4 +
        actualInnerShellKummerConstant mu theta * N / a ^ 2 ∧
    ‖actualInnerScaledKummerDefect mu theta a F qm r‖ ≤
      actualInnerShellEquationConstant * N / R ^ 4 +
        actualInnerShellKummerConstant mu theta * N / a ^ 2 := by
  have h := actual_Hartree_normalized_inner_shell_equation_bound F hF hcF R r hR hr
  exact ⟨actual_inner_scaled_Kummer_bound mu theta a R r _ F _
      (lt_of_lt_of_le hR hr) h.1.1 h.1.2.1 h.1.2.2,
    actual_inner_scaled_Kummer_bound mu theta a R r _ F _
      (lt_of_lt_of_le hR hr) h.2.1 h.2.2.1 h.2.2.2⟩

end HBL.TypeIIDynamicSelection
