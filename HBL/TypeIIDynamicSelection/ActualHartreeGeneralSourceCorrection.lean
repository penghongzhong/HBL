import HBL.TypeIIDynamicSelection.ActualHartreeCompleteObstructionBound

/-!
# A uniform compatible correction for arbitrary source data

The input is not restricted to the first core/radiation interaction.
Fp,Fm are arbitrary continuous sources in the original L^{2,7/4}(dr)
space; F is the complete outer RHS, and Q bounds r^2 |F| on its actual
interval. The same fixed Fredholm responses, full compatibility matrix
and physical velocity directions are used. Neither a small obstruction
nor a right-inverse estimate nor a residual-improvement step is assumed.

This is a frozen source-to-correction estimate. A later use for a PDE
residual must establish source coherence and all the other residual terms.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

/-- The actual complete Green coefficient is bounded by the radius-squared
source envelope, without a loss at the moving left endpoint. -/
theorem actual_general_source_Green_coefficient_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B r0 Q : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hQ : 0 ≤ Q)
    (hr0 : 0 < r0) (hOrder : r0 ≤ B) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume r0 B)
    (hEnvelope : ∀ r ∈ Icc r0 B, ‖F r‖ ≤ Q / r ^ 2) :
    IntervalIntegrable (originGreenSourceA K F) volume r0 B ∧
      ‖originGreenCoeffA K B F r0‖ ≤ (1 + (D + 1) * G * B ^ 2) * B * Q := by
  let C0 := 1 + (D + 1) * G * B ^ 2
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hK := origin_kummer_annulus_bound K r0 B G hr0 hBR hG hbound
  have hDensity (r : ℝ) (hr : r ∈ Icc r0 B) :
      ‖originGreenSourceA K F r‖ ≤ C0 * Q := by
    have hrp : 0 < r := hr0.trans_le hr.1
    have hW : originGreenWronskian K r =
        (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) :=
      origin_physical_wronskian_exact K ⟨hrp.le, hr.2.trans hBR.le⟩ hrp.ne'
    have hExp : ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, Complex.mul_im, pow_two]
    have hInv : ‖(originGreenWronskian K r)⁻¹‖ = r ^ 2 := by
      rw [hW, norm_inv, norm_mul, norm_pow, norm_inv, hExp, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
      simp
    have hreg := origin_kummer_regular_physical_bound K D G hD hG hBR.le
      hcoeff hbound r ⟨hrp, hr.2⟩
    rw [originGreenSourceA, div_eq_mul_inv, norm_mul, norm_mul, hInv]
    calc
      _ ≤ C0 * (Q / r ^ 2) * r ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hreg.1 (hEnvelope r hr) (norm_nonneg _) hC0) (sq_nonneg r)
      _ = C0 * Q := by field_simp [hrp.ne']
  have hIntegral : ‖originGreenCoeffA K B F r0‖ ≤ C0 * Q * |B - r0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    rw [uIoc_of_le hOrder] at hr
    exact hDensity r ⟨hr.1.le, hr.2⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hOrder)] at hIntegral
  refine ⟨(actual_origin_Green_source_integrability K hK hOrder F hF).1, ?_⟩
  calc
    _ ≤ C0 * Q * (B - r0) := hIntegral
    _ ≤ C0 * Q * B := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0 hQ)
    _ = _ := by dsimp [C0]; ring

/-- The same complete matrix constructs a unique real correction for
EVERY input pair and complete outer forcing in the displayed source class.
The output norm is controlled by original input norms, homogeneously.
Q is a bound for the raw outer source, not a bound for an unknown residual
or a hidden compatibility assumption. -/
theorem actual_Hartree_general_source_correction_region
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C : ℝ, 6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < C ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
      ∀ (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
        Continuous Fp → Continuous Fm →
      ∀ (F : ℝ → ℂ) (Q : ℝ), 0 ≤ Q →
        IntervalIntegrable F volume (L / a) B →
        (∀ r ∈ Icc (L / a) B, ‖F r‖ ≤ Q / r ^ 2) →
        let N0 := innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm
        |c| ≤ 1 ∧ L * |c| ≤ 1 ∧ 0 < L / a ∧ L / a ≤ B ∧
        ∃ p : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F p.1 p.2 = 0 ∧
          (∀ q : ℝ × ℝ,
            actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
              Fp Fm hp hm F q.1 q.2 = 0 → q = p) ∧
          innerWeightedNorm (7 / 4 : ℝ)
              (fun r => Fp r + p.2 * actualMomentLockedInnerPhaseSource L c r) +
            innerWeightedNorm (7 / 4 : ℝ)
              (fun r => Fm r + p.1 * actualMomentLockedInnerScaleSource L c r) ≤
            N0 + C * L ^ (-(1 / 2 : ℝ)) * (N0 + Q) := by
  obtain ⟨Lc, ec, _hLc, hec, hCancel⟩ :=
    actual_Hartree_moment_locked_coupled_unique_cancellation_region
      K D G hD hG hB hBR hcoeff hbound hsmallB
  obtain ⟨Li, ei, _hLi, hei, hInverse⟩ :=
    actual_Hartree_moment_locked_coupled_inverse_bound_region
      K D G hD hG hB hBR hcoeff hbound hsmallB
  obtain ⟨Cs, hCs, hSharp⟩ := actual_Hartree_moment_locked_sharp_source_obstruction_gain
  let CT := actualMomentLockedObstructionTraceConstant D G B
  let CK := 1 + (D + 1) * G * B ^ 2
  have hCT : 0 ≤ CT := by
    dsimp [CT, actualMomentLockedObstructionTraceConstant,
      actualInnerShellValueConstant, actualInnerShellDerivativeConstant]
    positivity
  have hCK : 0 ≤ CK := by dsimp [CK]; positivity
  let M := (1024 * Cs / B ^ 2) * (CT + CK * B)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let L0 := max Lc (max Li (6 + 1 / B))
  let epsilon := min ec (min ei 1)
  have hL0 : 6 ≤ L0 := by
    have hTail : 6 + 1 / B ≤ L0 := (le_max_right _ _).trans (le_max_right _ _)
    have hRecip : 0 ≤ 1 / B := by positivity
    linarith
  have hepsilon : 0 < epsilon := lt_min hec (lt_min hei (by norm_num))
  have hepsOne : epsilon ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨L0, epsilon, 1 + M, hL0, hepsilon, hepsOne, by positivity, ?_⟩
  intro L c a hLp hLarge ha3 hSmall Fp Fm hp hm hcp hcm F Q hQ hF hEnvelope
  dsimp only
  let N0 := innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm
  have hN0 : 0 ≤ N0 := add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hLsix : 6 ≤ L := hL0.trans hLarge
  have hLtwo : 2 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hLargeC : Lc ≤ L := (le_max_left _ _).trans hLarge
  have hLargeI : Li ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLarge)
  have hTail : 6 + 1 / B ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLarge)
  have hSmallC : a * |c| ≤ ec := hSmall.trans (min_le_left _ _)
  have hSmallI : a * |c| ≤ ei := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hLa : L ≤ a := by
    have hPow : L ≤ L ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hLone) (show 0 ≤ L ^ 2 + L by positivity)]
    exact hPow.trans ha3
  have haOne : 1 ≤ a := hLone.trans hLa
  have hLc : L * |c| ≤ 1 :=
    (mul_le_mul_of_nonneg_right hLa (abs_nonneg c)).trans (hSmall.trans hepsOne)
  have hc : |c| ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hLone (abs_nonneg c)
    nlinarith only [h, hLc]
  have hLB : L / a ≤ B := by
    apply (div_le_iff₀ ha).2
    have hRecip : 1 / B ≤ L := by linarith only [hTail]
    have hBL : 1 ≤ L * B := (div_le_iff₀ hB).1 hRecip
    have hBL2 := mul_le_mul_of_nonneg_left hBL (sq_nonneg L)
    have hALB := mul_le_mul_of_nonneg_right ha3 hB.le
    have hLsq : L ≤ L ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hLone) hLp.le]
    nlinarith only [hBL2, hALB, hLsq]
  have hr0 : 0 < L / a := div_pos hLp ha
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let Z := actualMomentLockedIntervalObstruction K (L / a) B F J.1 J.2
  have hTrace := actual_Hartree_canonical_baseline_outgoing_trace_bound
    K D G B L a hD hG hBR hLtwo ha3 hLB hcoeff hbound Fp Fm hp hm hcp hcm
  have hGreen := (actual_general_source_Green_coefficient_bound
    K D G B (L / a) Q hD hG hQ hr0 hLB hBR hcoeff hbound F hF hEnvelope).2
  have hZ : ‖Z‖ ≤ CT / a * N0 + CK * B * Q :=
    (norm_sub_le _ _).trans (_root_.add_le_add hTrace hGreen)
  have hCTerm : CT / a * N0 ≤ CT * (N0 + Q) :=
    (mul_le_mul_of_nonneg_right (div_le_self hCT haOne) hN0).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hQ) hCT)
  have hQTerm : CK * B * Q ≤ CK * B * (N0 + Q) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hN0) (mul_nonneg hCK hB.le)
  have hZtotal : ‖Z‖ ≤ (CT + CK * B) * (N0 + Q) :=
    (hZ.trans (_root_.add_le_add hCTerm hQTerm)).trans_eq (by ring)
  have hK := origin_kummer_annulus_bound K (L / a) B G hr0 hBR hG hbound
  obtain ⟨p, hColumns, hUnique⟩ := hCancel L c a hLp hLargeC ha3 hc hSmallC Z
  have hAffine (q : ℝ × ℝ) := actual_Hartree_moment_locked_full_coupled_response
    K hr0 hLB hK L c hLp a ha Fp Fm hp hm F hF q.1 q.2
  have hCompat : actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
      Fp Fm hp hm F p.1 p.2 = 0 := (hAffine p).trans hColumns
  have hSpeed := hInverse L c a hLp hLargeI ha3 hc hSmallI Fp Fm hp hm F hF p.1 p.2 hCompat
  have hAdjusted := hSharp L c a B hLone hLc ha3 hB Fp Fm hp hm p.1 p.2 Z hSpeed
  have hFactor : 0 ≤ (1024 * Cs / B ^ 2) * L ^ (-(1 / 2 : ℝ)) := by positivity
  refine ⟨hc, hLc, hr0, hLB, p, hCompat, ?_, ?_⟩
  · intro q hq
    exact hUnique q ((hAffine q).symm.trans hq)
  · calc
      _ ≤ N0 + (1024 * Cs / B ^ 2) * L ^ (-(1 / 2 : ℝ)) * ‖Z‖ := hAdjusted
      _ ≤ N0 + (1024 * Cs / B ^ 2) * L ^ (-(1 / 2 : ℝ)) *
          ((CT + CK * B) * (N0 + Q)) :=
        _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hZtotal hFactor)
      _ = N0 + M * L ^ (-(1 / 2 : ℝ)) * (N0 + Q) := by dsimp [M]; ring
      _ ≤ N0 + (1 + M) * L ^ (-(1 / 2 : ℝ)) * (N0 + Q) := by
        have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (show M ≤ 1 + M by linarith)
            (Real.rpow_nonneg hLp.le (-(1 / 2 : ℝ)))) (add_nonneg hN0 hQ)
        exact _root_.add_le_add le_rfl h

end HBL.TypeIIDynamicSelection
